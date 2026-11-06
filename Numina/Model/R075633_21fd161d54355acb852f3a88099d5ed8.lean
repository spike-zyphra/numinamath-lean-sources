import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_297269 {f : ℝ → ℝ} (hf : ∀ x ∈ Icc 0 1, |f x| ≤ 1)
  (h : ∃ a b c, f = λ x => a * x ^ 2 + b * x + c) :
  deriv f 0 ≤ 8 := by
  rcases h with ⟨a, b, c, heq⟩
  have h1 : deriv f 0 = b := by
    rw [heq]
    simp [deriv_pow, deriv_mul, deriv_id'', deriv_const, add_left_comm, mul_comm b, mul_assoc]
    all_goals norm_num
  have h2 := hf 0 (left_mem_Icc.mpr (by norm_num))
  simp [heq] at h2
  have h3 := hf 1 (right_mem_Icc.mpr (by norm_num))
  simp [heq] at h3
  have h4 := hf (1/2) (by norm_num [mem_Icc])
  simp [heq] at h4
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  cases' abs_le.mp h4 with h4_neg h4_pos
  linarith [h1, h2_neg, h2_pos, h3_neg, h3_pos, h4_neg, h4_pos]