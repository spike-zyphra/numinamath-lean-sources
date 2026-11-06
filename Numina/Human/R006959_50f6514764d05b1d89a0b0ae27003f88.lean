import Mathlib

theorem number_theory_129350 : 10001 ^ 2 = 100020001 ∧ 100010001 ^ 2 = 10002000300020001 ∧ √1000200030004000300020001 = 1000100010001 := by
  refine ⟨?_, ?_, ?_⟩
  . norm_num
  . norm_num
  . rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num