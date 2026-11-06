import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_281023 {a : ℕ → ℝ}
  (ha1 : a 1 = π / 6)
  (han : ∀ n, 0 < a n ∧ a n < π / 2)
  (h : ∀ n, tan (a (n + 1)) * cos (a n) = 1)
  (hm : ∏ k in Finset.Icc 1 m, sin (a k) = 1 / 100) :
  m = 3333 := by
  have h1 := h 0
  have h2 := han 0
  rcases h2 with ⟨ha0_pos, ha0_lt_pi_div_two⟩
  have h3 : a 1 = π / 6 := ha1
  have htan_a1 : tan (a 1) = 1 / Real.sqrt 3 := by
    rw [h3]
    have htan : tan (π / 6) = 1 / Real.sqrt 3 := by
      exact tan_pi_div_six
    exact htan
  have h4 : tan (a 1) * cos (a 0) = 1 := by 
    simpa using h1
  rw [htan_a1] at h4
  have h5 : cos (a 0) = Real.sqrt 3 := by
    field_simp at h4 ⊢
    <;> linarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (3 : ℝ) > 0),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)
    ]
  have hcos_a0_le_one : cos (a 0) ≤ 1 := by 
    apply cos_le_one
  have hcos_a0_eq_sqrt3 : cos (a 0) = Real.sqrt 3 := h5
  have h6 : Real.sqrt 3 ≤ (1 : ℝ) := by
    linarith [hcos_a0_le_one, hcos_a0_eq_sqrt3]
  have h7 : 1 < Real.sqrt 3 := by
    rw [Real.lt_sqrt] <;> norm_num
  linarith [h6, h7]