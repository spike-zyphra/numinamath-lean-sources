import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_111139 (a : ℝ) (f : ℝ → ℝ) (hf : f = λ x => a * x^3 + 3 * x^2 - x + 1)
  (h : ∀ x, deriv f x ≤ 0) :
  a ≤ -3 := by
  have h1 : ∀ x:ℝ, deriv f x = 3*a*x^2 + 6*x - 1 := by
    intro x
    rw [hf]
    simp [deriv_pow, deriv_const, deriv_add, deriv_sub, deriv_id', mul_comm]
    all_goals field_simp
    <;> ring_nf <;> field_simp
    <;> ring
  have h2 : ∀ x:ℝ, 3*a*x^2 + 6*x - 1 ≤ 0 := by
    intro x
    specialize h x
    rw [h1 x] at h 
    linarith
  by_cases ha : a ≤ 0
  · -- Case a ≤ 0.
    by_cases ha' : a < 0
    · -- Case a < 0.
      have h3 : a < 0 := ha'
      have h4 : ∀ x:ℝ, 3*a*x^2 + 6*x - 1 ≤ 0 := h2
      have h5 : -3/a - 1 ≤ 0 := by
        have h3' := h4 (-1/a)
        have h_eq : 3*a*(-1/a)^2 + 6*(-1/a) - 1 = -3/a - 1 := by
          have ha_nz : a ≠ 0 := by nlinarith
          field_simp [ha_nz]
          <;> ring_nf <;> field_simp [ha_nz]
          <;> ring
        linarith [h3', h_eq]
      have h6 : a ≤ -3 := by
        have h7 : a < 0 := h3
        have h8 : -3/a - 1 ≤ 0 := h5
        have h9 : -3/a ≤ 1 := by linarith
        have h10 : a < 0 := h3
        have h11 : -3 ≥ a := by
          apply (div_le_iff_of_neg' (by linarith)).mp at h9
          nlinarith
          all_goals nlinarith
        linarith
      linarith
    · -- Case a ≥ 0 and not a < 0, so a = 0
      have ha0 : a = 0 := by nlinarith
      rw [ha0] at h2
      have h3 := h2 1
      norm_num at h3
      all_goals linarith
  · -- Case a > 0
    have ha_pos : a > 0 := by linarith
    have h3 := h2 1
    nlinarith