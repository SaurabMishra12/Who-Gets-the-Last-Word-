/-
  AxiomAudit.lean
  Standalone diagnostic script for inspecting exported theorem types (`#check`)
  and kernel axiom dependencies (`#print axioms`) across all modules of
  `WhoGetsLastWord`.
  Run via: `lake env lean AxiomAudit.lean`
-/

import WhoGetsLastWord

open WhoGetsLastWord

-- 1. Communication Graph & Recipient Update Set (Eq. 1)
#check DirectedGraph.mem_recipientSet_iff
#print axioms DirectedGraph.mem_recipientSet_iff

#check DirectedGraph.isRecipient_inStar_of_ne_sink
#print axioms DirectedGraph.isRecipient_inStar_of_ne_sink

-- 2. Theorem A: One-Round Sink Invariance & Exact Resource Counts (Theorem 3.3 Part 1)
#check inNeighbors_inStar_eq_dense
#print axioms inNeighbors_inStar_eq_dense

#check incomingMessages_inStar_eq_dense
#print axioms incomingMessages_inStar_eq_dense

#check sinkInput_inStar_eq_dense
#print axioms sinkInput_inStar_eq_dense

#check sinkState_inStar_eq_dense
#print axioms sinkState_inStar_eq_dense

#check delivery_reduction_identity
#print axioms delivery_reduction_identity

#check update_reduction_identity
#print axioms update_reduction_identity

#check exact_two_thirds_reduction_N3
#print axioms exact_two_thirds_reduction_N3

-- 3. Theorem B: Readout Invariance & Pointwise Fallback Dominance (Theorem 3.3 Parts 2 & 3)
#check R_sink_inStar_eq_dense
#print axioms R_sink_inStar_eq_dense

#check R_sp_inStar_eq_dense
#print axioms R_sp_inStar_eq_dense

#check fallback_pointwise_gain_identity
#print axioms fallback_pointwise_gain_identity

#check fallback_dominates_sink_pointwise
#print axioms fallback_dominates_sink_pointwise

#check fallback_zero_additional_updates
#print axioms fallback_zero_additional_updates

#check expected_fallback_gain_identity
#print axioms expected_fallback_gain_identity

-- 4. Theorem C: Readout Duality & Synthesis Multiplicity (Theorem 3.4)
#check inStar_terminalProfile_characterization
#print axioms inStar_terminalProfile_characterization

#check R_aa_eq_if_nonSink_updates_unchanged
#print axioms R_aa_eq_if_nonSink_updates_unchanged

#check DualityWitness.readout_duality_verified_witness
#print axioms DualityWitness.readout_duality_verified_witness

#check paired_correctness_pointwise_identity
#print axioms paired_correctness_pointwise_identity

#check expected_paired_correctness_identity
#print axioms expected_paired_correctness_identity

-- 5. Theorem D: Plurality Abstention Veto & Specialist Recovery (Proposition 3.5)
#check pluralityVoteAsc_eq_of_strict_majority
#print axioms pluralityVoteAsc_eq_of_strict_majority

#check R_orig_eq_noanswer_of_majority_abstain
#print axioms R_orig_eq_noanswer_of_majority_abstain

#check R_orig_accuracy_zero_of_majority_abstain
#print axioms R_orig_accuracy_zero_of_majority_abstain

#check R_aa_eq_specialist_of_peers_abstain
#print axioms R_aa_eq_specialist_of_peers_abstain

#check prob_all_uninformed_abstain_eq
#print axioms prob_all_uninformed_abstain_eq

#check expected_acc_R_orig_upper_bound
#print axioms expected_acc_R_orig_upper_bound

#check expected_acc_R_aa_specialist_lower_bound
#print axioms expected_acc_R_aa_specialist_lower_bound

#check veto_limit_eps_zero
#print axioms veto_limit_eps_zero

-- 6. Propositions E & F: Support–Volume Coupling & Counterfactual Identities (Prop 3.1, Eqs. 2–3)
#check supportProj_linear_add
#print axioms supportProj_linear_add

#check supportProj_linear_smul
#print axioms supportProj_linear_smul

#check supportProj_idempotent
#print axioms supportProj_idempotent

#check supportProj_selfAdjoint
#print axioms supportProj_selfAdjoint

#check supportProj_orthogonal_complement
#print axioms supportProj_orthogonal_complement

#check realizedVol_bounds
#print axioms realizedVol_bounds

#check vol_support_change_identity
#print axioms vol_support_change_identity

#check expected_mediation_decomposition
#print axioms expected_mediation_decomposition

#check expected_residual_identity
#print axioms expected_residual_identity

-- 7. Adversarial Counterexamples (Section 11)
#check Counterexamples.two_round_breaks_sink_invariance
#print axioms Counterexamples.two_round_breaks_sink_invariance

#check Counterexamples.nondeterministic_decoding_breaks_sink_invariance
#print axioms Counterexamples.nondeterministic_decoding_breaks_sink_invariance

#check Counterexamples.message_ordering_breaks_prompt_invariance
#print axioms Counterexamples.message_ordering_breaks_prompt_invariance

#check Counterexamples.unanswerable_query_breaks_fallback_dominance
#print axioms Counterexamples.unanswerable_query_breaks_fallback_dominance

#check Counterexamples.fixed_sink_agrees_all_agent_votes_diverge
#print axioms Counterexamples.fixed_sink_agrees_all_agent_votes_diverge

#check Counterexamples.equal_nominal_cap_unequal_realized_volume
#print axioms Counterexamples.equal_nominal_cap_unequal_realized_volume

#check Counterexamples.equal_realized_volume_different_semantic_outcomes
#print axioms Counterexamples.equal_realized_volume_different_semantic_outcomes

#check Counterexamples.additional_updates_can_degrade_voting_accuracy
#print axioms Counterexamples.additional_updates_can_degrade_voting_accuracy
