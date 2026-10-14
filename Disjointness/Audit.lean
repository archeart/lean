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
