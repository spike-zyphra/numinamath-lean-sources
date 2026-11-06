import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12268 (f : ℝ → ℝ) (hf : f = λ x => 2 * sqrt x + 1 / x) :
    IsLeast {y | ∃ x > 0, f x = y} 3 := by 
  constructor
  · -- Show 3 is in the set
    use 1
    constructor
    · norm_num
    · -- Show that when x = 1, f x = 3
      rw [hf]
      simp
      <;> norm_num
  · -- Show 3 is minimal in the set
    intro y hy
    rcases hy with ⟨x, hx, h_eq⟩
    rw [hf] at h_eq 
    have h1 : 2 * sqrt x + 1 / x = y := by
      simpa using h_eq
    have h2 : 0 < x := by linarith
    have h3 : 2 * sqrt x + 1 / x ≥ 3 := by
      have hx1 : 0 < x := h2
      have h4 : 0 < sqrt x := by
        apply Real.sqrt_pos.mpr
        linarith
      have h5 : 2 * sqrt x + 1 / x - 3 ≥ 0 := by
        have h6 : (2 * sqrt x + 1 / x - 3) = (2 * x * sqrt x + 1 - 3 * x) / x := by
          field_simp
          <;> ring
        rw [h6] at *
        have h7 : 2 * x * sqrt x + 1 - 3 * x ≥ 0 := by
          nlinarith [sq_nonneg (sqrt x - 1), sq_nonneg (x - 1), sq_nonneg (2 * sqrt x - (x)), 
            Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), mul_pos (show 0 < sqrt x by apply Real.sqrt_pos.mpr (by linarith)) (show 0 < x by linarith)]
        have h8 : (2 * x * sqrt x + 1 - 3 * x) / x ≥ 0 := by
          apply div_nonneg
          linarith [h7]
          all_goals
            linarith
        linarith
      linarith
    linarith [h1, h3]