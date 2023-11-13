use crate::hash_to_curve::svdw_hash_to_curve;
use crate::{
    DkgCircuit, BIT_LEN_LIMB, DEFAULT_WINDOW_SIZE, NUMBER_OF_LIMBS, NUMBER_OF_LOOKUP_LIMBS,
};
use anyhow::Result;
use eth_types::{keccak256, Word};
use halo2_ecc::integer::rns::Rns;
use halo2wrong::curves::grumpkin::G1Affine as GkG1;
use halo2wrong::curves::{
    bn256::{self, Bn256, Fr as BnScalar, G1Affine as BnG1, G2Affine as BnG2},
    grumpkin, Coordinates, CurveAffine, CurveExt,
};
use halo2wrong::halo2::plonk::{keygen_pk, keygen_vk, ProvingKey, VerifyingKey};
use halo2wrong::halo2::poly::commitment::Params;
use halo2wrong::halo2::poly::kzg::commitment::ParamsKZG;
use halo2wrong::halo2::SerdeFormat;
use halo2wrong::utils::{big_to_fe, fe_to_big};
use std::fs::{metadata, File};
use std::io::BufReader;
use zkevm_circuits::util::word;

pub(crate) const DEFAULT_SERDE_FORMAT: SerdeFormat = SerdeFormat::RawBytesUnchecked;
pub(crate) const MAX_DEGREE: usize = 22;

pub fn mod_n<C: CurveAffine>(x: C::Base) -> C::Scalar {
    let x_big = fe_to_big(x);
    big_to_fe(x_big)
}

pub fn rns<C: CurveAffine>() -> Rns<C::Base, C::Scalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
    Rns::construct()
}

pub fn rns_setup<C: CurveAffine>(
    k_override: u32,
) -> (Rns<C::Base, C::Scalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, u32) {
    let rns = rns::<C>();
    let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;
    let mut k: u32 = (bit_len_lookup + 1) as u32;
    if k_override != 0 {
        k = k_override;
    }
    (rns, k)
}

pub fn hash_to_curve_bn<'a>(domain_prefix: &'a str) -> Box<dyn Fn(&[u8]) -> bn256::G1 + 'a> {
    svdw_hash_to_curve::<bn256::G1>(
        "bn256_g1",
        domain_prefix,
        <bn256::G1 as CurveExt>::Base::one(),
    )
}

pub fn hash_to_curve_grumpkin<'a>(
    domain_prefix: &'a str,
) -> Box<dyn Fn(&[u8]) -> grumpkin::G1 + 'a> {
    svdw_hash_to_curve::<grumpkin::G1>(
        "grumpkin_g1",
        domain_prefix,
        <grumpkin::G1 as CurveExt>::Base::one(),
    )
}

pub fn load_or_create_params(params_dir: &str, degree: usize) -> Result<ParamsKZG<Bn256>> {
    // read params
    let params_path = format!("{params_dir}/params{degree}");
    log::info!("load_params {}", params_path);
    if let Ok(params) = load_params(&params_path, degree, DEFAULT_SERDE_FORMAT) {
        return Ok(params);
    }

    // create params for degree
    let max_params_path = format!("{params_dir}/params{MAX_DEGREE}");
    log::info!("load_max_params {}", params_path);
    if let Ok(mut params) = load_params(&max_params_path, MAX_DEGREE, DEFAULT_SERDE_FORMAT) {
        if degree < MAX_DEGREE {
            params.downsize(degree as u32);

            let mut file = File::create(params_path)?;
            params.write_custom(&mut file, DEFAULT_SERDE_FORMAT)?;
        }
        return Ok(params);
    }

    return Err(anyhow::format_err!("download params{MAX_DEGREE} first"));
}

pub fn load_params(
    params_dir: &str,
    degree: usize,
    serde_format: SerdeFormat,
) -> Result<ParamsKZG<Bn256>> {
    log::info!("start loading params with degree {}", degree);
    let params_path = if metadata(params_dir)?.is_dir() {
        // auto load
        format!("{params_dir}/params{degree}")
    } else {
        params_dir.to_string()
    };
    let f = File::open(params_path)?;

    // check params file length:
    //   len: 4 bytes
    //   g: 2**DEGREE g1 points, each 32 bytes(256bits)
    //   g_lagrange: 2**DEGREE g1 points, each 32 bytes(256bits)
    //   g2: g2 point, 64 bytes
    //   s_g2: g2 point, 64 bytes
    let file_size = f.metadata()?.len();
    let g1_num = 2 * (1 << degree);
    let g2_num = 2;
    let g1_bytes_len = match serde_format {
        SerdeFormat::Processed => 32,
        SerdeFormat::RawBytes | SerdeFormat::RawBytesUnchecked => 64,
    };
    let g2_bytes_len = 2 * g1_bytes_len;
    let expected_len = 4 + g1_num * g1_bytes_len + g2_num * g2_bytes_len;
    if file_size != expected_len {
        return Err(anyhow::format_err!("invalid params file len {} for degree {}. check DEGREE or remove the invalid params file", file_size, degree));
    }

    let p = ParamsKZG::<Bn256>::read_custom::<_>(&mut BufReader::new(f), serde_format)?;
    log::info!("load params successfully!");
    Ok(p)
}

pub fn load_pk<const THRESHOLD: usize, const NUMBER_OF_MEMBERS: usize>(
    params_dir: &str,
    degree: usize,
    serde_format: SerdeFormat,
) -> Result<ProvingKey<bn256::G1Affine>> {
    log::info!("start loading pk with degree {}", degree);
    let pk_path = if metadata(params_dir)?.is_dir() {
        // auto load
        if cfg!(feature = "g2chip") {
            format!("{params_dir}/pk-g2-{THRESHOLD}-{NUMBER_OF_MEMBERS}-{degree}")
        } else {
            format!("{params_dir}/pk-{THRESHOLD}-{NUMBER_OF_MEMBERS}-{degree}")
        }
    } else {
        params_dir.to_string()
    };
    let f = File::open(pk_path)?;

    let pk = ProvingKey::read::<_, DkgCircuit<THRESHOLD, NUMBER_OF_MEMBERS>>(
        &mut BufReader::new(f),
        serde_format,
        #[cfg(feature = "circuit-params")]
        (),
    )?;
    log::info!("load pk successfully!");
    Ok(pk)
}

pub fn load_vk<const THRESHOLD: usize, const NUMBER_OF_MEMBERS: usize>(
    params_dir: &str,
    degree: usize,
    serde_format: SerdeFormat,
) -> Result<VerifyingKey<bn256::G1Affine>> {
    log::info!("start loading vk with degree {}", degree);
    let vk_path = if metadata(params_dir)?.is_dir() {
        // auto load
        if cfg!(feature = "g2chip") {
            format!("{params_dir}/vk-g2-{THRESHOLD}-{NUMBER_OF_MEMBERS}-{degree}")
        } else {
            format!("{params_dir}/vk-{THRESHOLD}-{NUMBER_OF_MEMBERS}-{degree}")
        }
    } else {
        params_dir.to_string()
    };
    let f = File::open(vk_path)?;

    let vk = VerifyingKey::read::<_, DkgCircuit<THRESHOLD, NUMBER_OF_MEMBERS>>(
        &mut BufReader::new(f),
        serde_format,
        #[cfg(feature = "circuit-params")]
        (),
    )?;
    log::info!("load vk successfully!");
    Ok(vk)
}

pub fn load_or_create_vk<const THRESHOLD: usize, const NUMBER_OF_MEMBERS: usize>(
    params_dir: &str,
    params: &ParamsKZG<Bn256>,
    degree: usize,
) -> Result<VerifyingKey<bn256::G1Affine>> {
    if !metadata(params_dir)?.is_dir() {
        return Err(anyhow::format_err!(
            "invalid file directory: {}",
            params_dir
        ));
    }

    if let Ok(vk) =
        load_vk::<THRESHOLD, NUMBER_OF_MEMBERS>(params_dir, degree, DEFAULT_SERDE_FORMAT)
    {
        return Ok(vk);
    }

    log::info!("load vk failed; create and store a new vk!");
    let circuit_dummy = DkgCircuit::<THRESHOLD, NUMBER_OF_MEMBERS>::dummy(DEFAULT_WINDOW_SIZE);
    let vk = keygen_vk(params, &circuit_dummy).expect("keygen_vk should not fail");
    let vk_path = {
        // auto load
        if cfg!(feature = "g2chip") {
            format!("{params_dir}/vk-g2-{THRESHOLD}-{NUMBER_OF_MEMBERS}-{degree}")
        } else {
            format!("{params_dir}/vk-{THRESHOLD}-{NUMBER_OF_MEMBERS}-{degree}")
        }
    };
    let mut f_vk = File::create(vk_path)?;
    vk.write(&mut f_vk, DEFAULT_SERDE_FORMAT)?;

    Ok(vk)
}

pub fn load_or_create_pk<const THRESHOLD: usize, const NUMBER_OF_MEMBERS: usize>(
    params_dir: &str,
    params: &ParamsKZG<Bn256>,
    degree: usize,
) -> Result<ProvingKey<bn256::G1Affine>> {
    if !metadata(params_dir)?.is_dir() {
        return Err(anyhow::format_err!(
            "invalid file directory: {}",
            params_dir
        ));
    }

    if let Ok(pk) =
        load_pk::<THRESHOLD, NUMBER_OF_MEMBERS>(params_dir, degree, DEFAULT_SERDE_FORMAT)
    {
        return Ok(pk);
    }

    log::info!("load pk failed; create and store a new vk and pk!");
    let vk = load_or_create_vk::<THRESHOLD, NUMBER_OF_MEMBERS>(params_dir, params, degree)?;
    let circuit_dummy = DkgCircuit::<THRESHOLD, NUMBER_OF_MEMBERS>::dummy(DEFAULT_WINDOW_SIZE);
    let pk = keygen_pk(params, vk, &circuit_dummy).expect("keygen_pk should not fail");
    let pk_path = {
        // auto load
        if cfg!(feature = "g2chip") {
            format!("{params_dir}/pk-g2-{THRESHOLD}-{NUMBER_OF_MEMBERS}-{degree}")
        } else {
            format!("{params_dir}/pk-{THRESHOLD}-{NUMBER_OF_MEMBERS}-{degree}")
        }
    };
    let mut f_pk = File::create(pk_path)?;
    pk.write(&mut f_pk, DEFAULT_SERDE_FORMAT)?;

    Ok(pk)
}

/// Return the bn256 G1 (x, y) coordinates in little endian bytes.
pub fn bn_g1_bytes_le(g: &BnG1) -> [u8; 64] {
    let g_coord = Option::<Coordinates<_>>::from(g.coordinates()).expect("point is the identity");
    let mut g_le = [0u8; 64];
    g_le[..32].copy_from_slice(&g_coord.x().to_bytes());
    g_le[32..].copy_from_slice(&g_coord.y().to_bytes());
    g_le
}

/// Return the bn256 G2 (x, y) coordinates in little endian bytes.
pub fn bn_g2_bytes_le(g: &BnG2) -> [u8; 128] {
    let g_coord = Option::<Coordinates<_>>::from(g.coordinates()).expect("point is the identity");
    let mut g_le = [0u8; 128];
    g_le[..64].copy_from_slice(&g_coord.x().to_bytes());
    g_le[64..].copy_from_slice(&g_coord.y().to_bytes());
    g_le
}

/// Return the grumpkin G (x, y) coordinates in little endian bytes.
pub fn gk_g1_bytes_le(g: &GkG1) -> [u8; 64] {
    let g_coord = Option::<Coordinates<_>>::from(g.coordinates()).expect("point is the identity");
    let mut g_le = [0u8; 64];
    g_le[..32].copy_from_slice(&g_coord.x().to_bytes());
    g_le[32..].copy_from_slice(&g_coord.y().to_bytes());
    g_le
}

pub fn keccak_digest_word(input: &[u8]) -> word::Word<BnScalar> {
    let digest = keccak256(input);
    word::Word::from(Word::from_big_endian(&digest))
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2wrong::halo2::poly::commitment::ParamsProver;

    #[test]
    fn test_hash_to_curve() {
        let hasher = hash_to_curve_bn("another generator");
        let h = hasher(b"second generator h");
        assert!(bool::from(h.is_on_curve()));

        let hasher = hash_to_curve_grumpkin("another generator");
        let h = hasher(b"second generator h");
        assert!(bool::from(h.is_on_curve()));
    }

    #[test]
    #[ignore]
    fn test_kzg_params() {
        let path = "./kzg_params";
        let degree = 18;
        let general_params =
            load_or_create_params(path, degree).expect("failed to load or create kzg params");
        let verifier_params = general_params.verifier_params();

        let vk = load_or_create_vk::<3, 5>("./kzg_params", &general_params, degree).unwrap();
        let pk = load_or_create_pk::<3, 5>("./kzg_params", &general_params, degree).unwrap();
        assert_eq!(
            vk.to_bytes(DEFAULT_SERDE_FORMAT),
            pk.get_vk().to_bytes(DEFAULT_SERDE_FORMAT)
        )
    }
}
