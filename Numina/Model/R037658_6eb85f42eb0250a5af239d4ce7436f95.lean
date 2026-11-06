import Mathlib

open Real Set
open scoped Real

theorem calculus_12149 : IsGreatest {y | ∃ x, y = cos x + 2 * sin x} (Real.sqrt 5) := by
  constructor
  · -- Show that √5 is in the set
    use (Real.arctan (2))
    have h1 : cos (Real.arctan (2)) = 1 / Real.sqrt 5 := by
      rw [cos_arctan]
      field_simp
      <;> nlinarith
    have h2 : sin (Real.arctan (2)) = 2 / Real.sqrt 5 := by
      rw [sin_arctan]
      field_simp
      <;> nlinarith
    rw [h1, h2]
    field_simp
    <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · -- Show that √5 is greatest in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h3 : cos x + 2 * sin x ≤ Real.sqrt 5 := by
      nlinarith [sq_nonneg (cos x * 2 - sin x), sq_nonneg (cos x - 2 * sin x), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (cos x - 1 / Real.sqrt 5), sq_nonneg (sin x - 2 / Real.sqrt 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), cos_sq_add_sin_sq x]
    have h4 : y = cos x + 2 * sin x := by
      linarith
    linarith [h4, h3]