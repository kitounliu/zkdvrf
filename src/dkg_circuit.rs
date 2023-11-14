use crate::ecc_chip::FixedPointChip;
#[cfg(feature = "g2chip")]
use crate::ecc_chip::{AssignedPoint2, FixedPoint2Chip};
use crate::grumpkin_chip::GrumpkinChip;
use crate::poseidon::P128Pow5T3Bn;
use crate::utils::keccak_digest_word;
use crate::{
    BIT_LEN_LIMB, LAST_BIT_LEN_LIMB, NUMBER_OF_LIMBS, POSEIDON_LEN, POSEIDON_RATE, POSEIDON_WIDTH,
};
use halo2_ecc::integer::rns::Rns;
#[cfg(feature = "g2chip")]
use halo2_ecc::integer::IntegerConfig;
use halo2_ecc::maingate::RegionCtx;
use halo2_ecc::{AssignedPoint, EccConfig};
use halo2_gadgets::poseidon::{
    primitives::ConstantLength, Hash as PoseidonHash, Pow5Chip, Pow5Config,
};
use halo2_maingate::{
    AssignedValue, MainGate, MainGateConfig, MainGateInstructions, RangeChip, RangeConfig,
    RangeInstructions,
};
#[cfg(feature = "g2chip")]
use halo2wrong::curves::bn256::G2Affine as BnG2;
use halo2wrong::curves::{
    bn256::{Fq as BnBase, Fr as BnScalar, G1Affine as BnG1},
    ff::PrimeField,
    grumpkin::G1Affine as GkG1,
};
use halo2wrong::halo2::arithmetic::Field;
use halo2wrong::halo2::circuit::Chip;
use halo2wrong::halo2::plonk::{Advice, Column, Expression, SecondPhase, Selector};
use halo2wrong::halo2::poly::Rotation;
use halo2wrong::halo2::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error as PlonkError},
};
use num::Integer;
use std::iter;
use zkevm_circuits::keccak_circuit::{KeccakCircuit, KeccakCircuitConfig, KeccakCircuitConfigArgs};
use zkevm_circuits::util::{word::Word, Expr, SubCircuit, SubCircuitConfig};
use zkevm_circuits::{table::KeccakTable, util::Challenges};

fn keccak_input_len<const NUMBER_OF_MEMBERS: usize>() -> usize {
    let mut len = 128 + NUMBER_OF_MEMBERS * 160;

    #[cfg(feature = "g2chip")]
    {
        len += 128;
    }

    len
}

#[derive(Clone, Debug)]
pub struct DkgCircuitConfig {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
    poseidon_config: Pow5Config<BnScalar, POSEIDON_WIDTH, POSEIDON_RATE>,
    q_rlc_keccak_input: Selector,
    rlc: Column<Advice>,
    // Keccak
    q_keccak: Selector,
    challenges: Challenges,
    keccak_config: KeccakCircuitConfig<BnScalar>,
}

impl DkgCircuitConfig {
    pub fn new<const NUMBER_OF_MEMBERS: usize>(meta: &mut ConstraintSystem<BnScalar>) -> Self {
        let rns = Rns::<BnBase, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::construct();
        let main_gate_config = MainGate::<BnScalar>::configure(meta);
        let mut overflow_bit_lens = rns.overflow_lengths();
        let mut composition_bit_lens = vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS];

        let keccak_bit_lens = 8usize;
        composition_bit_lens.push(keccak_bit_lens);
        let keccak_overflow_bit_lens = BnScalar::NUM_BITS as usize % keccak_bit_lens;
        overflow_bit_lens.push(keccak_overflow_bit_lens);

        let range_config = RangeChip::<BnScalar>::configure(
            meta,
            &main_gate_config,
            composition_bit_lens,
            overflow_bit_lens,
        );

        let challenges = Challenges::construct(meta);
        let challenges_expr = challenges.exprs(meta);

        // poseidon configure
        let main_advices = main_gate_config.advices();
        let state = main_advices[0..POSEIDON_WIDTH].to_vec();
        let partial_sbox = main_advices[POSEIDON_WIDTH];

        let rc_a = (0..POSEIDON_WIDTH)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>();
        let rc_b = (0..POSEIDON_WIDTH)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>();
        meta.enable_constant(rc_b[0]);

        let poseidon_config = Pow5Chip::configure::<P128Pow5T3Bn>(
            meta,
            state.try_into().unwrap(),
            partial_sbox,
            rc_a.try_into().unwrap(),
            rc_b.try_into().unwrap(),
        );

        // keccak configure
        let keccak_table = KeccakTable::construct(meta);
        // RLC
        let q_rlc_keccak_input = meta.selector();
        let rlc = meta.advice_column_in(SecondPhase);
        meta.enable_equality(rlc);

        Self::configure_rlc(
            meta,
            "keccak_input_rlc",
            main_gate_config.clone(),
            q_rlc_keccak_input,
            rlc,
            challenges_expr.keccak_input(),
        );

        let keccak_input_len = keccak_input_len::<NUMBER_OF_MEMBERS>();
        let q_keccak = meta.complex_selector();
        meta.lookup_any("keccak", |meta| {
            // Layout:
            // | q_keccak |     a    |    b      |    rlc  |
            // | -------- |--------- | --------- | ------- |
            // |     1    | word_lo  |  word_hi  |    rlc  |
            let q_keccak = meta.query_selector(q_keccak);
            let word_lo = meta.query_advice(main_gate_config.advices()[0], Rotation::cur());
            let word_hi = meta.query_advice(main_gate_config.advices()[1], Rotation::cur());
            let input = [
                q_keccak.clone(),
                q_keccak.clone() * meta.query_advice(rlc, Rotation::cur()),
                q_keccak.clone() * keccak_input_len.expr(),
                q_keccak.clone() * word_lo,
                q_keccak * word_hi,
            ];
            let table = [
                keccak_table.is_enabled,
                keccak_table.input_rlc,
                keccak_table.input_len,
                keccak_table.output.lo(),
                keccak_table.output.hi(),
            ]
            .map(|column| meta.query_advice(column, Rotation::cur()));

            input.into_iter().zip(table).collect()
        });

        let keccak_config = {
            let challenges = challenges.exprs(meta);
            KeccakCircuitConfig::new(
                meta,
                KeccakCircuitConfigArgs {
                    keccak_table,
                    challenges,
                },
            )
        };

        DkgCircuitConfig {
            main_gate_config,
            range_config,
            poseidon_config,
            q_rlc_keccak_input,
            rlc,
            q_keccak,
            challenges,
            keccak_config,
        }
    }

    // config modified from https://github.com/privacy-scaling-explorations/zkevm-circuits/blob/main/zkevm-circuits/src/tx_circuit/sign_verify.rs#L208
    fn configure_rlc(
        meta: &mut ConstraintSystem<BnScalar>,
        name: &'static str,
        main_gate_config: MainGateConfig,
        q_rlc: Selector,
        rlc: Column<Advice>,
        challenge: Expression<BnScalar>,
    ) {
        // Layout (take input with length 12 as an example)
        // | q_rlc |                          rlc                        |   a   |   b   |   c   |   d    |   e    |
        // | ----- | --------------------------------------------------- | ----- | ----- | ----- | ------ | ------ |
        // |   1   |                                                   0 |     0 |     0 |     0 |  be[0] |  be[1] |
        // |   1   |                                  be[0]*r^1 +  be[1] | be[2] | be[3] | be[4] |  be[5] |  be[6] |
        // |   1   | be[0]*r^6  + be[1]*r^5  + ... +  be[5]*r^1 +  be[6] | be[7] | be[8] | be[9] | be[10] | be[11] |
        // |   0   | be[0]*r^11 + be[1]*r^10 + ... + be[10]*r^1 + be[11] |       |       |       |        |        |
        //
        // Note that the first row of zeros will be enforced by copy constraint.
        meta.create_gate(name, |meta| {
            let q_rlc = meta.query_selector(q_rlc);
            let [a, b, c, d, e] = main_gate_config
                .advices()
                .map(|column| meta.query_advice(column, Rotation::cur()));
            let [rlc, rlc_next] = [Rotation::cur(), Rotation::next()]
                .map(|rotation| meta.query_advice(rlc, rotation));
            let inputs = [rlc, a, b, c, d, e];

            vec![q_rlc * (rlc_next - Self::rlc_expr(&inputs, challenge))]
        });
    }

    fn rlc_expr<F: Field>(
        expressions: &[Expression<F>],
        randomness: Expression<F>,
    ) -> Expression<F> {
        if !expressions.is_empty() {
            let init = expressions[0].clone();
            expressions
                .iter()
                .skip(1)
                .fold(init, |acc, expr| acc * randomness.clone() + expr.clone())
        } else {
            Expression::Constant(F::ZERO)
        }
    }

    pub fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    #[cfg(feature = "g2chip")]
    fn integer_config(&self) -> IntegerConfig {
        IntegerConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub fn range_chip<N: PrimeField>(&self) -> RangeChip<N> {
        RangeChip::new(self.range_config.clone())
    }

    pub fn main_gate<N: PrimeField>(&self) -> MainGate<N> {
        MainGate::new(self.main_gate_config.clone())
    }

    pub fn grumpkin_chip(&self) -> GrumpkinChip {
        GrumpkinChip::new(self.main_gate_config.clone())
    }
}

#[derive(Clone)]
pub struct DkgCircuit<const THRESHOLD: usize, const NUMBER_OF_MEMBERS: usize> {
    coeffs: [Value<BnScalar>; THRESHOLD],
    random: Value<BnScalar>,
    public_keys: [Value<GkG1>; NUMBER_OF_MEMBERS],
    window_size: usize,
    grumpkin_aux_generator: Value<GkG1>,
    hash: Word<Value<BnScalar>>,
    keccak_input: Vec<Value<BnScalar>>,
    keccak_circuit: KeccakCircuit<BnScalar>,
}

impl<const THRESHOLD: usize, const NUMBER_OF_MEMBERS: usize>
    DkgCircuit<THRESHOLD, NUMBER_OF_MEMBERS>
{
    pub fn new(
        coeffs: Vec<Value<BnScalar>>,
        random: Value<BnScalar>,
        public_keys: Vec<Value<GkG1>>,
        window_size: usize,
        grumpkin_aux_generator: Value<GkG1>,
        keccak_input_bytes: Vec<u8>,
    ) -> Self {
        assert_eq!(coeffs.len(), THRESHOLD);
        assert_eq!(public_keys.len(), NUMBER_OF_MEMBERS);

        let hash = keccak_digest_word(&keccak_input_bytes).into_value();
        let keccak_input: Vec<_> = keccak_input_bytes
            .iter()
            .map(|byte| Value::known(BnScalar::from(*byte as u64)))
            .collect();
        let keccak_circuit = KeccakCircuit::new(0, vec![keccak_input_bytes]);

        DkgCircuit {
            coeffs: coeffs
                .try_into()
                .expect("unable to convert coefficient vector"),
            random,
            public_keys: public_keys
                .try_into()
                .expect("unable to convert public key vector"),
            window_size,
            grumpkin_aux_generator,
            hash,
            keccak_input,
            keccak_circuit,
        }
    }

    pub fn dummy(window_size: usize) -> Self {
        let coeffs: Vec<_> = (0..THRESHOLD).map(|_| Value::unknown()).collect();
        let random = Value::unknown();
        let public_keys: Vec<_> = (0..NUMBER_OF_MEMBERS).map(|_| Value::unknown()).collect();
        let grumpkin_aux_generator = Value::unknown();

        let keccak_len = keccak_input_len::<NUMBER_OF_MEMBERS>();
        let keccak_input_bytes: Vec<_> = (0..keccak_len).map(|_| 0u8).collect();
        let hash = Word::new([Value::unknown(); 2]);
        let keccak_input: Vec<_> = (0..keccak_len).map(|_| Value::unknown()).collect();
        let keccak_circuit = KeccakCircuit::new(0, vec![keccak_input_bytes]);

        DkgCircuit {
            coeffs: coeffs
                .try_into()
                .expect("unable to convert coefficient vector"),
            random,
            public_keys: public_keys
                .try_into()
                .expect("unable to convert public key vector"),
            window_size,
            grumpkin_aux_generator,
            hash,
            keccak_input,
            keccak_circuit,
        }
    }

    fn keccak_decompose_assigned_values(
        &self,
        assigned_values: &[&AssignedValue<BnScalar>],
        main_gate: &MainGate<BnScalar>,
        range_chip: &RangeChip<BnScalar>,
        layouter: &mut impl Layouter<BnScalar>,
    ) -> Result<Vec<AssignedValue<BnScalar>>, PlonkError> {
        let mut decomposed = vec![];
        for &assigned in assigned_values.iter() {
            let res = layouter.assign_region(
                || "decompose assigned bn scalar for keccak",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let value = assigned.value().map(|v| *v);
                    let (assigned_again, decomposed) =
                        range_chip.decompose(ctx, value, 8, BnScalar::NUM_BITS as usize)?;
                    main_gate.assert_equal(ctx, &assigned, &assigned_again)?;

                    Ok(decomposed)
                },
            )?;
            decomposed.extend(res);
        }

        Ok(decomposed)
    }

    fn keccak_decompose_bn_limb(
        &self,
        limb: &AssignedValue<BnScalar>,
        bit_len: usize,
        main_gate: &MainGate<BnScalar>,
        range_chip: &RangeChip<BnScalar>,
        layouter: &mut impl Layouter<BnScalar>,
    ) -> Result<Vec<AssignedValue<BnScalar>>, PlonkError> {
        layouter.assign_region(
            || "decompose bn limb for keccak",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let value = limb.value().map(|v| *v);
                let (assigned, decomposed) = range_chip.decompose(ctx, value, 8, bit_len)?;
                main_gate.assert_equal(ctx, &assigned, &limb)?;

                Ok(decomposed)
            },
        )
    }

    fn keccak_decompose_bn_g1(
        &self,
        g: AssignedPoint<BnBase, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        main_gate: &MainGate<BnScalar>,
        range_chip: &RangeChip<BnScalar>,
        layouter: &mut impl Layouter<BnScalar>,
    ) -> Result<Vec<AssignedValue<BnScalar>>, PlonkError> {
        let x_limbs: Vec<AssignedValue<BnScalar>> =
            g.x().limbs().iter().map(|l| l.into()).collect();
        let y_limbs: Vec<AssignedValue<BnScalar>> =
            g.y().limbs().iter().map(|l| l.into()).collect();

        let mut decomposed = vec![];
        for limbs in [x_limbs, y_limbs].iter() {
            for i in 0..NUMBER_OF_LIMBS {
                let bit_len = if i < NUMBER_OF_LIMBS - 1 {
                    BIT_LEN_LIMB
                } else {
                    LAST_BIT_LEN_LIMB
                };

                let res = self.keccak_decompose_bn_limb(
                    &limbs[i], bit_len, main_gate, range_chip, layouter,
                )?;
                decomposed.extend(res);
            }
        }

        Ok(decomposed)
    }

    #[cfg(feature = "g2chip")]
    fn keccak_decompose_bn_g2(
        &self,
        g2: AssignedPoint2<BnBase, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        main_gate: &MainGate<BnScalar>,
        range_chip: &RangeChip<BnScalar>,
        layouter: &mut impl Layouter<BnScalar>,
    ) -> Result<Vec<AssignedValue<BnScalar>>, PlonkError> {
        let x0 = &g2.x().i0;
        let x1 = &g2.x().i1;
        let y0 = &g2.y().i0;
        let y1 = &g2.y().i1;

        let mut decomposed = vec![];
        for a in [x0, x1, y0, y1] {
            let limbs: Vec<AssignedValue<BnScalar>> = a.limbs().iter().map(|l| l.into()).collect();
            for i in 0..NUMBER_OF_LIMBS {
                let bit_len = if i < NUMBER_OF_LIMBS - 1 {
                    BIT_LEN_LIMB
                } else {
                    LAST_BIT_LEN_LIMB
                };

                let res = self.keccak_decompose_bn_limb(
                    &limbs[i], bit_len, main_gate, range_chip, layouter,
                )?;
                decomposed.extend(res);
            }
        }

        Ok(decomposed)
    }

    fn assign_rlc(
        &self,
        input_values: &[Value<BnScalar>],
        input_assigned: &[AssignedValue<BnScalar>],
        config: &DkgCircuitConfig,
        main_gate: &MainGate<BnScalar>,
        challenges: &Challenges<Value<BnScalar>>,
        layouter: &mut impl Layouter<BnScalar>,
    ) -> Result<AssignedValue<BnScalar>, PlonkError> {
        layouter.assign_region(
            || "assign rlc for keccak",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let advices = main_gate.config().advices();
                let mut rlc = Value::known(BnScalar::ZERO);
                let keccak_rand = challenges.keccak_input();

                let zero = main_gate.assign_constant(ctx, BnScalar::ZERO)?;

                let input_pairs: Vec<_> = input_assigned
                    .iter()
                    .zip(input_values.iter())
                    .map(|(x, y)| (x.cell(), *y))
                    .collect();
                let input_padded: Vec<_> =
                    iter::repeat_with(|| (zero.cell(), Value::known(BnScalar::ZERO)))
                        .take(
                            Integer::next_multiple_of(&input_pairs.len(), &advices.len())
                                - input_pairs.len(),
                        )
                        .chain(input_pairs.into_iter())
                        .collect();

                for (chunk_idx, chunk) in input_padded.chunks_exact(advices.len()).enumerate() {
                    ctx.enable(config.q_rlc_keccak_input)?;
                    let assigned_rlc =
                        ctx.assign_advice(|| format!("hash_rlc[{chunk_idx}]"), config.rlc, rlc)?;
                    for ((idx, column), &term) in
                        (chunk_idx * chunk.len()..).zip(advices).zip(chunk)
                    {
                        let copied = ctx.assign_advice(
                            || format!("keccak_input_byte[{idx}]"),
                            column,
                            term.1,
                        )?;

                        ctx.constrain_equal(term.0, copied.cell())?;
                    }
                    if chunk_idx == 0 {
                        ctx.constrain_equal(zero.cell(), assigned_rlc.cell())?;
                    }

                    rlc = chunk
                        .iter()
                        .map(|term| term.1)
                        .fold(rlc, |acc, input| acc * keccak_rand + input);
                    ctx.next();
                }

                let assigned_rlc = ctx.assign_advice(|| "final_hash_rlc", config.rlc, rlc)?;
                Ok(assigned_rlc)
            },
        )
    }

    fn enable_keccak_lookup(
        &self,
        config: &DkgCircuitConfig,
        rlc: &AssignedValue<BnScalar>,
        hash: &Word<Value<BnScalar>>,
        layouter: &mut impl Layouter<BnScalar>,
    ) -> Result<Word<AssignedValue<BnScalar>>, PlonkError> {
        let hash_lo = hash.lo();
        let hash_hi = hash.hi();

        layouter.assign_region(
            || "enable keccak lookup",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                ctx.enable(config.q_keccak)?;
                let copied = ctx.assign_advice(|| "rlc", config.rlc, rlc.value().copied())?;
                ctx.constrain_equal(rlc.cell(), copied.cell())?;

                let assigned_hash_lo =
                    ctx.assign_advice(|| "hash_lo", config.main_gate_config.advices()[0], hash_lo)?;
                let assigned_hash_hi =
                    ctx.assign_advice(|| "hash_hi", config.main_gate_config.advices()[1], hash_hi)?;

                Ok(Word::new([assigned_hash_lo, assigned_hash_hi]))
            },
        )
    }
}

impl<const THRESHOLD: usize, const NUMBER_OF_MEMBERS: usize> Circuit<BnScalar>
    for DkgCircuit<THRESHOLD, NUMBER_OF_MEMBERS>
{
    type Config = DkgCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<BnScalar>) -> Self::Config {
        DkgCircuitConfig::new::<NUMBER_OF_MEMBERS>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<BnScalar>,
    ) -> Result<(), PlonkError> {
        let challenges = config.challenges.values(&mut layouter);
        self.keccak_circuit
            .synthesize_sub(&config.keccak_config, &challenges, &mut layouter)?;
        let range_chip = config.range_chip::<BnScalar>();
        range_chip.load_table(&mut layouter)?;

        let ecc_chip_config = config.ecc_chip_config();
        let mut fixed_chip =
            FixedPointChip::<BnG1, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(ecc_chip_config);

        #[cfg(feature = "g2chip")]
        let integer_config = config.integer_config();
        #[cfg(feature = "g2chip")]
        let mut fixed2_chip =
            FixedPoint2Chip::<BnBase, BnG2, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(integer_config);

        let main_gate = config.main_gate::<BnScalar>();
        let mut grumpkin_chip = config.grumpkin_chip();

        let (shares, a) = layouter.assign_region(
            || "region compute shares from coefficients",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let mut coeffs = vec![];
                for a in self.coeffs.iter() {
                    let a_assigned = main_gate.assign_value(ctx, *a)?;
                    coeffs.push(a_assigned);
                }

                let mut shares = vec![];

                // compute s0
                let mut s0 = coeffs[0].clone();
                for j in 1..THRESHOLD {
                    s0 = main_gate.add(ctx, &s0, &coeffs[j])?;
                }
                shares.push(s0);

                for i in 2..=NUMBER_OF_MEMBERS {
                    let ii = BnScalar::from(i as u64);
                    let x = main_gate.assign_constant(ctx, ii)?;
                    let mut s = coeffs[THRESHOLD - 1].clone();
                    for j in (0..THRESHOLD - 1).rev() {
                        s = main_gate.mul_add(ctx, &s, &x, &coeffs[j])?;
                    }
                    shares.push(s);
                }

                Ok((shares, coeffs[0].clone()))
            },
        )?;

        layouter.assign_region(
            || "assign fixed point window table for bn256 chip",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);
                let g = BnG1::generator();
                fixed_chip.assign_fixed_point(ctx, &g, self.window_size)?;

                #[cfg(feature = "g2chip")]
                let g2 = BnG2::generator();
                #[cfg(feature = "g2chip")]
                fixed2_chip.assign_fixed_point(ctx, &g2, self.window_size)?;

                Ok(())
            },
        )?;

        layouter.assign_region(
            || "assign aux values for grumpkin chip",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);
                grumpkin_chip.assign_aux_generator(ctx, self.grumpkin_aux_generator)?;
                grumpkin_chip.assign_aux_correction(ctx)?;
                Ok(())
            },
        )?;

        let ga = layouter.assign_region(
            || "region ecc mul g1^a",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let ga = fixed_chip.mul(ctx, &a)?;
                // normalise for public inputs
                let ga = fixed_chip.normalize(ctx, &ga)?;

                Ok(ga)
            },
        )?;

        let mut keccak_input_bytes =
            self.keccak_decompose_bn_g1(ga, &main_gate, &range_chip, &mut layouter)?;

        for i in 0..NUMBER_OF_MEMBERS {
            let gs = layouter.assign_region(
                || "region ecc mul g1^s",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    // gs = g^s
                    let gs = fixed_chip.mul(ctx, &shares[i])?;
                    // normalise for public inputs
                    let gs = fixed_chip.normalize(ctx, &gs)?;
                    Ok(gs)
                },
            )?;

            let res = self.keccak_decompose_bn_g1(gs, &main_gate, &range_chip, &mut layouter)?;
            keccak_input_bytes.extend(res);
        }

        let (bits, gr) = layouter.assign_region(
            || "region grumpkin ecc mul g^r",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let g = grumpkin_chip.assign_constant(ctx, GkG1::generator())?;

                // we don't care about the value of r; if r==0, add will fail
                let bits = grumpkin_chip.to_bits_unsafe(ctx, &self.random)?;
                // gr = g^r
                let gr = grumpkin_chip.mul_bits(ctx, &g, &bits)?;

                Ok((bits, gr))
            },
        )?;

        let res = self.keccak_decompose_assigned_values(
            &[gr.x(), gr.y()],
            &main_gate,
            &range_chip,
            &mut layouter,
        )?;
        keccak_input_bytes.extend(res);

        for i in 0..NUMBER_OF_MEMBERS {
            let (pkr, pk) = layouter.assign_region(
                || "region grumpkin ecc mul encryption",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let pk = grumpkin_chip.assign_point(ctx, self.public_keys[i])?;
                    // pkr = pk^r
                    let pkr = grumpkin_chip.mul_bits(ctx, &pk, &bits)?;

                    Ok((pkr, pk))
                },
            )?;

            let res = self.keccak_decompose_assigned_values(
                &[pk.x(), pk.y()],
                &main_gate,
                &range_chip,
                &mut layouter,
            )?;
            keccak_input_bytes.extend(res);

            let message = [pkr.x, pkr.y];

            let poseidon_chip = Pow5Chip::construct(config.poseidon_config.clone());
            let hasher = PoseidonHash::<
                _,
                _,
                P128Pow5T3Bn,
                ConstantLength<POSEIDON_LEN>,
                POSEIDON_WIDTH,
                POSEIDON_RATE,
            >::init(poseidon_chip, layouter.namespace(|| "poseidon init"))?;
            let key = hasher.hash(layouter.namespace(|| "hash"), message)?;

            let cipher = layouter.assign_region(
                || "region add",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);
                    main_gate.add(ctx, &shares[i], &key)
                },
            )?;

            let res = self.keccak_decompose_assigned_values(
                &[&cipher],
                &main_gate,
                &range_chip,
                &mut layouter,
            )?;
            keccak_input_bytes.extend(res);
        }

        // compute g2^a
        #[cfg(feature = "g2chip")]
        let g2a = layouter.assign_region(
            || "region mul",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let g2a = fixed2_chip.mul(ctx, &a)?;
                let g2a = fixed2_chip.normalize(ctx, &g2a)?;

                Ok(g2a)
            },
        )?;

        #[cfg(feature = "g2chip")]
        {
            let res = self.keccak_decompose_bn_g2(g2a, &main_gate, &range_chip, &mut layouter)?;
            keccak_input_bytes.extend(res);
        }

        // assign rlc from keccak_input_bytes
        assert_eq!(self.keccak_input.len(), keccak_input_bytes.len());

        let assigned_rlc = self.assign_rlc(
            &self.keccak_input,
            &keccak_input_bytes,
            &config,
            &main_gate,
            &challenges,
            &mut layouter,
        )?;

        // enable keccak lookup
        let assigned_hash =
            self.enable_keccak_lookup(&config, &assigned_rlc, &self.hash, &mut layouter)?;

        main_gate.expose_public(layouter.namespace(|| "hash low"), assigned_hash.lo(), 0)?;
        main_gate.expose_public(layouter.namespace(|| "hash high"), assigned_hash.hi(), 1)?;

        Ok(())
    }
}
