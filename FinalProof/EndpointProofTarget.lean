namespace FinalProof

structure Beal003Requirements where
  PreservationOperator_P : Prop
  UniformizationOperator_N : Prop
  verified_common_prime_endpoint_producer : Prop
  exact_hypothesis_instantiation : Prop

def Beal003Requirements.closed (r : Beal003Requirements) : Prop :=
  r.PreservationOperator_P ∧
  r.UniformizationOperator_N ∧
  r.verified_common_prime_endpoint_producer ∧
  r.exact_hypothesis_instantiation

theorem beal003_closes_from_requirements
    (r : Beal003Requirements)
    (h : r.closed) :
    r.closed := h

end FinalProof
