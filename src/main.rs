use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::field::extension::Extendable;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig, AlgebraicHasher};
use plonky2::recursion::dummy_circuit::cyclic_base_proof;
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::RichField;
use plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data;


// Useful example hash chain test: https://docs.rs/plonky2/latest/src/plonky2/recursion/cyclic_recursion.rs.html#1-354

// Generates `CommonCircuitData` usable for recursion.
fn common_data_for_recursion<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>() -> CommonCircuitData<F, D>
where
C::Hasher: AlgebraicHasher<F>,
{
    let config = CircuitConfig::standard_recursion_config();
    let builder = CircuitBuilder::<F, D>::new(config);
    let data = builder.build::<C>();
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data =
        builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    let data = builder.build::<C>();

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data =
        builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    while builder.num_gates() < 1 << 12 {
        builder.add_gate(NoopGate, vec![]);
    }
    builder.build::<C>().common
}

// Toy example: Add One circuit (add one to the initial value in every recursive step)
// Layout:
// - Initial value
// - Result value
// - Recursive chain length
// New Layout (Balance circuit that verifies proofs for the previous balance and the token_in):
// - balance_old
// - balance_new
// - token_in
// - token_out
// - counter
fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    // START OF CIRCUIT
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let one = builder.one();
    let zero = builder.zero();
    
    // TODO find some is_le or do it ourselves to compare old balance and token_out
    // (honestly should do the same for safety with token_in)
    // Register the public inputs
    let balance_old = builder.add_virtual_public_input();
    let balance_new = builder.add_virtual_public_input();
    let token_in = builder.add_virtual_public_input();
    let token_out = builder.add_virtual_public_input();
    let counter = builder.add_virtual_public_input();

    // Infer recursive verification conditons from balance_old and token_in (if they are 0 we don't need a
    // previous proof)
    let balance_old_is_zero = builder.is_equal(balance_old, zero);
    let token_in_is_zero = builder.is_equal(token_in, zero);
    

    let mut common_data = common_data_for_recursion::<F, C, D>();
    // This can only be called once...
    let verifier_data_target = builder.add_verifier_data_public_inputs();
    common_data.num_public_inputs = builder.num_public_inputs();

    // VERIFY THE PROOF FOR balance_old AND token_in
    // NOTE: We can't do both at the same time when the assertion in
    // https://docs.rs/plonky2/latest/plonky2/plonk/circuit_builder/struct.CircuitBuilder.html#method.add_verifier_data_public_inputs
    // is not relaxed so we can call builder.add_verifier_data_public_inputs multiple times (or
    // circumvent it any other way). Possible solution here: https://github.com/polymerdao/plonky2-ed25519/blob/main/src/main.rs

    // Unpack inner proof's public inputs.
    let inner_cyclic_proof_with_pis = builder.add_virtual_proof_with_pis(&common_data);
    let inner_cyclic_pis = &inner_cyclic_proof_with_pis.public_inputs;
    let inner_cyclic_balance_old = inner_cyclic_pis[0];
    let inner_cyclic_balance_new = inner_cyclic_pis[1];
    let inner_cyclic_token_in = inner_cyclic_pis[2];
    let inner_cyclic_token_out = inner_cyclic_pis[3];
    let inner_cyclic_counter = inner_cyclic_pis[4];

    // The old_balance has to be the previous output if we have an inner proof for the balance or zero.
    let previous_balance_new =
        builder.select(balance_old_is_zero, inner_cyclic_balance_new, zero);
    builder.connect(balance_old, previous_balance_new);

    // Our chain length will be inner_counter + 1 if we have an inner proof, or 1 if not.
    let new_counter = builder.mul_add(balance_old_is_zero.target, inner_cyclic_counter, one);
    builder.connect(counter, new_counter);

    builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
        balance_old_is_zero,
        &inner_cyclic_proof_with_pis,
        &common_data,
        )?;
    let cyclic_circuit_data = builder.build::<C>();
    // END OF THE CIRCUIT

    // IVC
    // first initial proof with recursively verifying a dummy proof
    let mut pw = PartialWitness::new();
    let initial_targets = [];
    let initial_targets_pis = initial_targets.into_iter().enumerate().collect();
    pw.set_proof_with_pis_target::<C, D>(
        &inner_cyclic_proof_with_pis,
        &cyclic_base_proof(
            &common_data,
            &cyclic_circuit_data.verifier_only,
            initial_targets_pis,
            ),
            );
    pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    let proof = cyclic_circuit_data.prove(pw)?;
    check_cyclic_proof_verifier_data(
        &proof,
        &cyclic_circuit_data.verifier_only,
        &cyclic_circuit_data.common,
        )?;
    cyclic_circuit_data.verify(proof.clone())?;
    println!("Starting value: {}\nOutput: {}\nCounter: {}",proof.public_inputs[0], proof.public_inputs[1], proof.public_inputs[2]);

    // 1st recursive layer.
    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&inner_cyclic_proof_with_pis, &proof);
    pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    let proof = cyclic_circuit_data.prove(pw)?;
    check_cyclic_proof_verifier_data(
        &proof,
        &cyclic_circuit_data.verifier_only,
        &cyclic_circuit_data.common,
        )?;
    cyclic_circuit_data.verify(proof.clone())?;
    println!("Starting value: {}\nOutput: {}\nCounter: {}",proof.public_inputs[0], proof.public_inputs[1], proof.public_inputs[2]);

    // 2nd recursive layer.
    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&inner_cyclic_proof_with_pis, &proof);
    pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    let proof = cyclic_circuit_data.prove(pw)?;
    check_cyclic_proof_verifier_data(
        &proof,
        &cyclic_circuit_data.verifier_only,
        &cyclic_circuit_data.common,
        )?;
    println!("Starting value: {}\nOutput: {}\nCounter: {}",proof.public_inputs[0], proof.public_inputs[1], proof.public_inputs[2]);
    cyclic_circuit_data.verify(proof)
}
