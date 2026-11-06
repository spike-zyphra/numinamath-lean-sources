import Mathlib

theorem algebra_97437 : (0.48017 * 0.48017 * 0.48017 - 0.110)^2 < (0.48017 * 0.48017 * 0.48017 - 0.011)^2 ∧
    (0.48017 * 0.48017 * 0.48017 - 0.110)^2 < (0.48017 * 0.48017 * 0.48017 - 1.10)^2 ∧
    (0.48017 * 0.48017 * 0.48017 - 0.110)^2 < (0.48017 * 0.48017 * 0.48017 - 11.0)^2 ∧
    (0.48017 * 0.48017 * 0.48017 - 0.110)^2 < (0.48017 * 0.48017 * 0.48017 - 110)^2 := by 
  constructor
  · -- Prove the first inequality
    norm_num
    <;> try { native_decide }
  constructor
  · -- Prove the second inequality
    norm_num
    <;> try { native_decide }
  constructor
  · -- Prove the third inequality
    norm_num
    <;> try { native_decide }
  · -- Prove the fourth inequality
    norm_num
    <;> try { native_decide }