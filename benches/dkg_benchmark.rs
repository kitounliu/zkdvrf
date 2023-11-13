use criterion::{criterion_group, Criterion};

mod dkg_benches {
    use super::*;
    use ark_std::{end_timer, start_timer};
    use halo2wrong::curves::bn256::{Bn256, G1Affine as BnG1};
    use halo2wrong::halo2::plonk::{create_proof, keygen_pk, keygen_vk, verify_proof};
    use halo2wrong::halo2::poly::commitment::ParamsProver;
    use halo2wrong::halo2::poly::kzg::commitment::{
        KZGCommitmentScheme, ParamsKZG, ParamsVerifierKZG,
    };
    use halo2wrong::halo2::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
    use halo2wrong::halo2::poly::kzg::strategy::SingleStrategy;
    use halo2wrong::halo2::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    };
    use halo2wrong::utils::DimensionMeasurement;
    use rand_core::OsRng;
    use zkdvrf::{DkgCircuit, DkgMemberParams, MemberKey};

    fn dkg_proof_verify<
        const THRESHOLD: usize,
        const NUMBER_OF_MEMBERS: usize,
        const DEGREE: usize,
    >(
        c: &mut Criterion,
    ) {
        let mut rng = OsRng;

        let mut members = vec![];
        let mut pks = vec![];
        for _ in 0..NUMBER_OF_MEMBERS {
            let member = MemberKey::new(&mut rng);
            pks.push(member.get_public_key());
            members.push(member);
        }

        let dkg_params =
            DkgMemberParams::<THRESHOLD, NUMBER_OF_MEMBERS>::new(1, &pks, &mut rng).unwrap();
        let (circuit, instance) = dkg_params.circuit(&mut rng);
        let instance_ref = instance.iter().map(|i| i.as_slice()).collect::<Vec<_>>();

        let dimension = DimensionMeasurement::measure(&circuit).unwrap();
        println!("dimention: {:?}", dimension);

        let start1 = start_timer!(|| format!("kzg setup with degree {}", DEGREE));
        let general_params = ParamsKZG::<Bn256>::setup(DEGREE as u32, &mut rng);
        let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();
        end_timer!(start1);

        let vk = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&general_params, vk, &circuit).expect("keygen_pk should not fail");

        let mut transcript = Blake2bWrite::<_, BnG1, Challenge255<_>>::init(vec![]);

        let proof_message = format!("dkg prove with degree = {}", DEGREE);
        let start2 = start_timer!(|| proof_message);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<BnG1>,
            OsRng,
            Blake2bWrite<Vec<u8>, BnG1, Challenge255<BnG1>>,
            DkgCircuit<THRESHOLD, NUMBER_OF_MEMBERS>,
        >(
            &general_params,
            &pk,
            &[circuit],
            &[instance_ref.as_slice()],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        println!("proof size = {:?}", proof.len());

        c.bench_function("dkg proof verification", move |b| {
            b.iter(|| {
                let mut verifier_transcript =
                    Blake2bRead::<_, BnG1, Challenge255<_>>::init(&proof[..]);
                let strategy = SingleStrategy::new(&general_params);
                verify_proof::<
                    KZGCommitmentScheme<Bn256>,
                    VerifierSHPLONK<'_, Bn256>,
                    Challenge255<BnG1>,
                    Blake2bRead<&[u8], BnG1, Challenge255<BnG1>>,
                    SingleStrategy<'_, Bn256>,
                >(
                    &verifier_params,
                    pk.get_vk(),
                    strategy,
                    &[instance_ref.as_slice()],
                    &mut verifier_transcript,
                )
                .expect("failed to verify dkg circuit")
            })
        });
    }

    #[cfg(not(feature = "g2chip"))]
    criterion_group! {
        name = dkg_benches;
        config = Criterion::default();
        targets =
            dkg_proof_verify::<5,9,18>,
    //        dkg_proof_verify::<11,20,19>,
    //        dkg_proof_verify::<22,42,20>,
    //        dkg_proof_verify::<44,87,21>,
    //        dkg_proof_verify::<88,175,22>,
    }

    #[cfg(feature = "g2chip")]
    criterion_group! {
        name = dkg_benches;
        config = Criterion::default();
        targets =
            dkg_proof_verify::<3,4,18>,
    //        dkg_proof_verify::<9,16,19>,
    //        dkg_proof_verify::<20,38,20>,
    //        dkg_proof_verify::<42,82,21>,
    //        dkg_proof_verify::<86,170,22>,
    }
}

criterion::criterion_main!(dkg_benches::dkg_benches);
