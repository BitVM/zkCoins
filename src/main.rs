use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::field::extension::Extendable;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig,VerifierOnlyCircuitData, CommonCircuitData};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;

type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

fn prove_statement<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>() -> Result<ProofTuple<F, C, D>> {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // The arithmetic circuit.
    let x = builder.add_virtual_target();
    let a = builder.mul(x, x);
    let b = builder.mul_const(F::from_canonical_u32(4), x);
    let c = builder.mul_const(F::NEG_ONE, b);
    let d = builder.add(a, c);
    let e = builder.add_const(d, F::from_canonical_u32(7));

    // Public inputs are the initial value (provided below) and the result (which is generated).
    builder.register_public_input(x);
    builder.register_public_input(e);
    let mut pw = PartialWitness::new();
    pw.set_target(x, F::from_canonical_u32(1));
    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    Ok((proof, data.verifier_only, data.common))
}

/// An example of using Plonky2 to prove a statement of the form
/// "I know x² - 4x + 7".
fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    
    let (proof, verifier_only_data, common_data) = prove_statement::<F, C, D>()?;

    println!(
        "x² - 4 *x + 7 where x = {} is {}",
        proof.public_inputs[0],
        proof.public_inputs[1]
    );
    verifier_only_data.verify(proof)
}
