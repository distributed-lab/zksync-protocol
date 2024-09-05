use super::*;
use crate::witness::artifacts::LogQueueStates;
use crate::zkevm_circuits::base_structures::log_query::*;
use crate::zkevm_circuits::bn254::ec_pairing::input::{
    EcPairingCircuitFSMInputOutputWitness, EcPairingCircuitInputOutputWitness,
    EcPairingCircuitInstanceWitness, EcPairingFunctionFSMWitness,
};
use circuit_definitions::boojum::gadgets::non_native_field::implementations::implementation_u16::FFProxyValue;
use circuit_definitions::encodings::*;
use circuit_definitions::zk_evm::zk_evm_abstractions::precompiles::ecpairing::ECPairingRoundWitness;
use circuit_definitions::zkevm_circuits::bn254::ec_pairing::EcPairingPrecompileCallParamsWitness;
use circuit_definitions::zkevm_circuits::bn254::{BN256Fq, BN256Fq12NNField};

pub(crate) fn ecpairing_memory_queries(
    ecpairing_witnesses: &Vec<(u32, LogQuery_, ECPairingRoundWitness)>,
) -> Vec<MemoryQuery> {
    let amount_of_queries = ecpairing_witnesses
        .iter()
        .fold(0, |inner, (_, _, witness)| {
            inner + witness.reads.len() + witness.writes.len()
        });

    let mut ecpairing_memory_queries = Vec::with_capacity(amount_of_queries);

    for (_cycle, _query, witness) in ecpairing_witnesses.iter() {
        let initial_memory_len = ecpairing_memory_queries.len();

        // we read, then write
        ecpairing_memory_queries.extend_from_slice(&witness.reads);
        ecpairing_memory_queries.extend_from_slice(&witness.writes);

        assert_eq!(ecpairing_memory_queries.len() - initial_memory_len, 8);
    }
    ecpairing_memory_queries
}

// we want to simulate splitting of data into many separate instances of the same circuit.
// So we basically need to reconstruct the FSM state on input/output, and passthrough data.
// In practice the only difficulty is buffer state, everything else is provided by out-of-circuit VM

pub(crate) fn ecpairing_decompose_into_per_circuit_witness<
    F: SmallField,
    R: BuildableCircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    ecpairing_memory_queries: Vec<MemoryQuery>,
    ecpairing_simulator_snapshots: Vec<SimulatorSnapshot<F, FULL_SPONGE_QUEUE_STATE_WIDTH>>,
    ecpairing_memory_states: Vec<QueueStateWitness<F, FULL_SPONGE_QUEUE_STATE_WIDTH>>,
    ecpairing_witnesses: Vec<(u32, LogQuery_, ECPairingRoundWitness)>,
    ecpairing_queries: Vec<LogQuery_>,
    mut demuxed_ecpairing_queue: LogQueueStates<F>,
    num_rounds_per_circuit: usize,
    round_function: &R,
) -> Vec<EcPairingCircuitInstanceWitness<F>> {
    todo!("Compute internal FSM state");

    // assert_eq!(
    //     ecpairing_memory_queries.len(),
    //     ecpairing_memory_states.len()
    // );
    //
    // let memory_simulator_before = &ecpairing_simulator_snapshots[0];
    // assert_eq!(
    //     amount_of_memory_queries_before,
    //     memory_simulator_before.num_items as usize
    // );
    //
    // let mut result = vec![];
    //
    // let precompile_calls = ecpairing_queries;
    // let simulator_witness: Vec<_> = demuxed_ecpairing_queue.simulator.witness.clone().into();
    // let round_function_witness = ecpairing_witnesses;
    //
    // // check basic consistency
    // assert!(precompile_calls.len() == demuxed_ecpairing_queue.states_accumulator.len());
    // drop(demuxed_ecpairing_queue.states_accumulator);
    // assert!(precompile_calls.len() == round_function_witness.len());
    //
    // if precompile_calls.len() == 0 {
    //     return (vec![], amount_of_memory_queries_before);
    // }
    //
    // let mut round_counter = 0;
    // let num_requests = precompile_calls.len();
    //
    // // convension
    // let mut log_queue_input_state =
    //     take_queue_state_from_simulator(&demuxed_ecpairing_queue.simulator);
    // let amount_ecpairing_memory_queries = ecpairing_memory_queries.len();
    // let mut memory_queries_it = ecpairing_memory_queries.into_iter();
    //
    // let mut memory_read_witnesses = vec![];
    // let mut starting_request_idx = 0;
    //
    // let mut memory_queue_input_state = memory_simulator_before.take_sponge_like_queue_state();
    // let mut current_memory_queue_state = memory_queue_input_state.clone();
    //
    // let mut memory_queue_states_it = ecpairing_memory_states.iter();
    //
    // for (request_idx, (request, per_request_work)) in precompile_calls
    //     .into_iter()
    //     .zip(round_function_witness.into_iter())
    //     .enumerate()
    // {
    //     let _ = demuxed_ecpairing_queue
    //         .simulator
    //         .pop_and_output_intermediate_data(round_function);
    //
    //     let mut memory_reads_per_request = vec![];
    //
    //     let (_cycle, _req, round_witness) = per_request_work;
    //     assert_eq!(request, _req);
    //
    //     use crate::zk_evm::zk_evm_abstractions::precompiles::precompile_abi_in_log;
    //     let mut precompile_request = precompile_abi_in_log(request);
    //     let is_last_request = request_idx == num_requests - 1;
    //
    //     let mut amount_of_queries = 0;
    //     // we have 6 reads
    //     for (_query_index, read) in round_witness.reads.into_iter().enumerate() {
    //         let read_query = memory_queries_it.next().unwrap();
    //         assert!(read == read_query);
    //         assert!(read_query.rw_flag == false);
    //         memory_reads_per_request.push(read_query.value);
    //
    //         current_memory_queue_state =
    //             transform_sponge_like_queue_state(*memory_queue_states_it.next().unwrap());
    //
    //         precompile_request.input_memory_offset += 1;
    //         amount_of_queries += 1;
    //     }
    //
    //     // and 2 writes
    //     for (_query_index, write) in round_witness.writes.into_iter().enumerate() {
    //         let write_query = memory_queries_it.next().unwrap();
    //         assert!(write == write_query);
    //         assert!(write_query.rw_flag == true);
    //
    //         current_memory_queue_state =
    //             transform_sponge_like_queue_state(*memory_queue_states_it.next().unwrap());
    //
    //         precompile_request.output_memory_offset += 1;
    //         amount_of_queries += 1;
    //     }
    //
    //     assert_eq!(amount_of_queries, 6);
    //     round_counter += 1;
    //
    //     if round_counter == num_rounds_per_circuit || is_last_request {
    //         round_counter = 0;
    //
    //         let finished = is_last_request;
    //         if finished {
    //             assert!(memory_queries_it.next().is_none());
    //         }
    //
    //         let range = starting_request_idx..(request_idx + 1);
    //         let wit: VecDeque<_> = (&simulator_witness[range])
    //             .iter()
    //             .map(|el| (log_query_into_circuit_log_query_witness(&el.2), el.1))
    //             .collect();
    //
    //         let current_reads = std::mem::take(&mut memory_reads_per_request);
    //         let mut current_witness = std::mem::take(&mut memory_read_witnesses);
    //         current_witness.push(current_reads);
    //
    //         let mut observable_input_data = PrecompileFunctionInputData::placeholder_witness();
    //         if result.len() == 0 {
    //             observable_input_data.initial_memory_queue_state = memory_queue_input_state.clone();
    //             observable_input_data.initial_log_queue_state = log_queue_input_state.clone();
    //         }
    //
    //         let mut observable_output_data = PrecompileFunctionOutputData::placeholder_witness();
    //         if finished {
    //             observable_output_data.final_memory_state = current_memory_queue_state.clone();
    //         }
    //
    //
    //         // TODO: compute it
    //         let internal_fsm = EcPairingFunctionFSMWitness {
    //             read_precompile_call: false,
    //             read_words_for_round: false,
    //             completed: false,
    //             pairing_inner_state: todo!(),
    //             timestamp_to_use_for_read: request.timestamp.0,
    //             timestamp_to_use_for_write: request.timestamp.0 + 1,
    //             precompile_call_params: EcPairingPrecompileCallParamsWitness {
    //                 input_page: precompile_request.memory_page_to_read,
    //                 input_offset: precompile_request.input_memory_offset,
    //                 output_page: precompile_request.memory_page_to_write,
    //                 output_offset: precompile_request.output_memory_offset,
    //                 num_pairs: 0,
    //             },
    //         };
    //
    //         let witness = EcPairingCircuitInstanceWitness::<F> {
    //             closed_form_input: EcPairingCircuitInputOutputWitness::<F> {
    //                 start_flag: result.len() == 0,
    //                 completion_flag: finished,
    //                 observable_input: observable_input_data,
    //                 observable_output: observable_output_data,
    //                 hidden_fsm_input: EcPairingCircuitFSMInputOutputWitness::<F> {
    //                     internal_fsm: internal_fsm.clone(),
    //                     log_queue_state: log_queue_input_state.clone(),
    //                     memory_queue_state: memory_queue_input_state,
    //                 },
    //                 hidden_fsm_output: EcPairingCircuitFSMInputOutputWitness::<F> {
    //                     internal_fsm,
    //                     log_queue_state: take_queue_state_from_simulator(
    //                         &demuxed_ecpairing_queue.simulator,
    //                     ),
    //                     memory_queue_state: current_memory_queue_state.clone(),
    //                 },
    //             },
    //             requests_queue_witness: CircuitQueueRawWitness::<
    //                 F,
    //                 LogQuery<F>,
    //                 4,
    //                 LOG_QUERY_PACKED_WIDTH,
    //             > {
    //                 elements: wit,
    //             },
    //             memory_reads_witness: current_witness
    //                 .into_iter()
    //                 .map(|el| el.try_into().expect("length must match"))
    //                 .collect(),
    //         };
    //
    //         // make non-inclusize
    //         starting_request_idx = request_idx + 1;
    //
    //         result.push(witness);
    //
    //         log_queue_input_state =
    //             take_queue_state_from_simulator(&demuxed_ecpairing_queue.simulator);
    //         memory_queue_input_state = current_memory_queue_state.clone();
    //     }
    //
    //     if !memory_reads_per_request.is_empty() {
    //         // we may have drained it already if it was the end of the circuit
    //         memory_read_witnesses.push(memory_reads_per_request);
    //     }
    // }
    //
    // let memory_simulator_after = &ecpairing_simulator_snapshots[1];
    // let amount_of_memory_queries_after =
    //     amount_of_memory_queries_before + amount_ecpairing_memory_queries;
    //
    // assert_eq!(
    //     amount_of_memory_queries_after,
    //     memory_simulator_after.num_items as usize
    // );
    //
    // (result, amount_of_memory_queries_after)
}