module

import Disjointness

/-! Run with `lake lean Audit.lean`. A target proposition is printed for review;
printing its definition is not a proof that it holds. -/

#print Disjointness.FiniteLowerBoundClaim
#print axioms Disjointness.Integration.pmf_chain_rule
#print axioms Disjointness.Integration.pmf_condMutualInfo_nonneg
#print axioms Disjointness.Integration.pmf_condMutualInfo_le_log_card
#print axioms Disjointness.Integration.pmf_condMutualInfo_eq_sum
#print axioms Disjointness.Integration.pmf_condEntropy_pair_le
#print axioms Disjointness.Integration.pmf_condMutualInfo_bitvec_le
#print axioms Disjointness.Integration.pmf_klDiv_eq_zero_iff
#print axioms Disjointness.Tree.run
#print axioms Disjointness.Protocol.Correct
#print axioms Disjointness.Protocol.cost
#print axioms Disjointness.Tree.depth_comap
#print axioms Disjointness.Tree.run_comap
#print axioms Disjointness.Tree.decode_run
#print axioms Disjointness.Tree.run_length_le_depth
#print axioms Disjointness.Tree.run_mem_leafPaths
#print axioms Disjointness.Tree.card_leafPaths_le
#print axioms Disjointness.Tree.run_transcript_eq_iff
#print axioms Disjointness.Tree.transcript_cross
#print axioms Disjointness.Protocol.viewLaw_eq_bind_private
#print axioms Disjointness.Protocol.viewLaw_apply
#print axioms Disjointness.Protocol.privateTranscriptLaw_factorization
#print axioms Disjointness.Protocol.viewLaw_factorization
#print axioms Disjointness.Protocol.privateTranscriptLaw_support
#print axioms Disjointness.Protocol.depth_le_cost
#print axioms Disjointness.Protocol.run_length_le_cost
#print axioms Disjointness.Protocol.card_leafPaths_le_cost
#print axioms Disjointness.SendInput.depth_tree
#print axioms Disjointness.SendInput.output_tree
#print axioms Disjointness.sendInputProtocol_cost
#print axioms Disjointness.sendInputProtocol_outputLaw
#print axioms Disjointness.sendInputProtocol_correct

/-! Phase 3: probability, information cost, and public-seed conditioning. -/
#print axioms Disjointness.FiniteLaw.sum_pmf
#print axioms Disjointness.FiniteLaw.joint_apply
#print axioms Disjointness.FiniteLaw.joint_eq_bind
#print axioms Disjointness.FiniteLaw.joint_map_fst
#print axioms Disjointness.FiniteLaw.joint_fiber
#print axioms Disjointness.FiniteLaw.joint_cond_fst
#print axioms Disjointness.FiniteLaw.joint_const_toMeasure
#print axioms Disjointness.FiniteLaw.pi_apply
#print axioms Disjointness.FiniteLaw.pi_toMeasure
#print axioms Disjointness.FiniteLaw.pi_map_eval
#print axioms Disjointness.FiniteLaw.map_cond_preimage
#print axioms Disjointness.FiniteLaw.map_equiv_apply
#print axioms Disjointness.FiniteLaw.indep_pullback
#print axioms Disjointness.FiniteLaw.iIndep_pullback
#print axioms Disjointness.InformationTools.cond_chain
#print axioms Disjointness.InformationTools.cond_pair_le
#print axioms Disjointness.InformationTools.condMutualInfo_identDistrib
#print axioms Disjointness.InformationTools.condEntropy_le_of_fiber_support
#print axioms Disjointness.InformationTools.condMutualInfo_le_of_fiber_support
#print axioms Disjointness.Switch.fair_apply
#print axioms Disjointness.Switch.switches_apply
#print axioms Disjointness.Switch.switches_pos
#print axioms Disjointness.Switch.inputLaw_apply
#print axioms Disjointness.Switch.law_apply
#print axioms Disjointness.Switch.cond_switch
#print axioms Disjointness.Switch.inputLaw_indep
#print axioms Disjointness.Switch.inputLaw_map_coordinates
#print axioms Disjointness.Switch.inputLaw_iIndep
#print axioms Disjointness.Switch.coordinates_condIndep
#print axioms Disjointness.Switch.players_condIndep
#print axioms Disjointness.Switch.disj_of_mem_support
#print axioms Disjointness.Switch.law_map_triples
#print axioms Disjointness.Switch.law_map_coordinate
#print axioms Disjointness.Switch.coordinate_input_probabilities
#print axioms Disjointness.Switch.switches_iIndep
#print axioms Disjointness.Switch.switches_map_coordinate
#print axioms Disjointness.Protocol.executionLaw_view
#print axioms Disjointness.Protocol.executionLaw_indep
#print axioms Disjointness.Protocol.informationCost_nonneg
#print axioms Disjointness.Protocol.informationCost_eq_sum
#print axioms Disjointness.Protocol.informationCost_le
#print axioms Disjointness.Protocol.bjksInformationCost_nonneg
#print axioms Disjointness.Protocol.bjksInformationCost_le
#print axioms Disjointness.Protocol.seedLaw_eq_joint
#print axioms Disjointness.Protocol.seedLaw_apply
#print axioms Disjointness.Protocol.executionLaw_regroup
#print axioms Disjointness.Protocol.executionLaw_conditioning
#print axioms Disjointness.Protocol.conditional_inputLaw
#print axioms Disjointness.Protocol.conditioning_fiber
#print axioms Disjointness.Protocol.conditional_zero_of_publicLaw_zero
#print axioms Disjointness.Protocol.bjks_coordinates_condIndep
#print axioms Disjointness.Protocol.bjks_players_condIndep

#print Disjointness.Protocol.informationCost
#print Disjointness.Protocol.bjksInformationCost
#check Disjointness.Protocol.bjksInformationCost_le

/-! Phase 4: finite distances and the AND information theorem. -/
#print axioms Disjointness.Hellinger.sqDist_triangle
#print axioms Disjointness.Hellinger.cut_and_paste
#print axioms Disjointness.Hellinger.variation_sq_le
#print axioms Disjointness.Hellinger.event_difference_le
#print axioms Disjointness.Hellinger.sqrt_sub_sq_le_log
#print axioms Disjointness.Hellinger.sqDist_le_two_jensenShannon
#print axioms Disjointness.Channel.information_eq_entropy
#print axioms Disjointness.Channel.information_fair
#print axioms Disjointness.Channel.information_map
#print axioms Disjointness.Protocol.finiteViewLaw_rectangle
#print axioms Disjointness.Protocol.informationCost_eq_channel
#print axioms Disjointness.Protocol.and_information_lower_bound
#check Disjointness.Protocol.and_information_lower_bound

/-! Phases 5–7: embeddings, endpoints, and normalization. -/
#print axioms Disjointness.InformationTools.condEntropy_vector_le
#print axioms Disjointness.InformationTools.sum_mutualInfo_le
#print axioms Disjointness.Protocol.sum_coordinateInformation_le
#print axioms Disjointness.Protocol.bjksInformationCost_ge_sum_coordinates
#print axioms Disjointness.Protocol.localRandomize_cost
#print axioms Disjointness.Protocol.localRandomize_seedLaw
#print axioms Disjointness.Protocol.localRandomize_viewLaw
#print axioms Disjointness.Protocol.localRandomize_outputLaw
#print axioms Disjointness.FiniteLaw.map_equiv_injective
#print axioms Disjointness.FiniteLaw.joint_map_second
#print axioms Disjointness.FiniteLaw.pi_split
#print axioms Disjointness.FiniteLaw.pi_restrict
#print axioms Disjointness.FiniteLaw.pi_replace
#print axioms Disjointness.Switch.switches_resample
#print axioms Disjointness.Switch.average_resample
#print axioms Disjointness.Switch.disj_fill
#print axioms Disjointness.Protocol.embed_cost
#print axioms Disjointness.Protocol.embed_outputLaw
#print axioms Disjointness.Protocol.embed_correct
#print axioms Disjointness.Switch.inputLaw_fill
#print axioms Disjointness.Switch.joint_fill_channel
#print axioms Disjointness.Protocol.embed_branch_information
#print axioms Disjointness.Protocol.embed_informationCost
#print axioms Disjointness.Protocol.coordinate_average_lower_bound
#print axioms Disjointness.Protocol.bjks_information_lower_bound
#print axioms Disjointness.lowerBoundConstant_pos
#print axioms Disjointness.disjointness_lower_bound
#print axioms Disjointness.finiteLowerBoundClaim
#print axioms Disjointness.Tree.depth_truncate_le
#print axioms Disjointness.Tree.run_truncate
#print axioms Disjointness.Protocol.truncate_cost_le
#print axioms Disjointness.Protocol.truncate_outputLaw
#print axioms Disjointness.Protocol.truncate_correct
#print axioms Disjointness.disjointness_lower_bound_of_length
#print axioms Disjointness.BoundedTree.depth_le
#print axioms Disjointness.BoundedTree.toTree_encode
#print axioms Disjointness.BoundedTree.protocol_cost_le
#print axioms Disjointness.BoundedTree.protocol_outputLaw
#print axioms Disjointness.random_tape_disjointness_lower_bound
#print axioms Disjointness.random_tree_disjointness_lower_bound
#check Disjointness.disjointness_lower_bound
#check Disjointness.disjointness_lower_bound_of_length
#check Disjointness.random_tape_disjointness_lower_bound
#check Disjointness.random_tree_disjointness_lower_bound
#print Disjointness.BoundedTree.Code
