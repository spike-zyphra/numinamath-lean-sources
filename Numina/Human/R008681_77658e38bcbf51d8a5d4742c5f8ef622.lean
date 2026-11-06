import Mathlib

/- The solution set of the inequality $x^2 + 2x < 3$ is expressed as ______. (The answer should be expressed in the form of a set) -/
theorem algebra_9137 : {x | x ^ 2 + 2 * x < 3} = {x | -3 < x ∧ x < 1} := by
  -- Prove set equality by mutual inclusion
  ext y
  constructor <;> intro h
  all_goals simp_all
  . -- Prove the forward direction: if x^2 + 2x < 3, then -3 < x < 1
    constructor <;> nlinarith
  . -- Prove the backward direction: if -3 < x < 1, then x^2 + 2x < 3
    nlinarith
