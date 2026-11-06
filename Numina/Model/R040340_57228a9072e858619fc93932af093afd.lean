import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_175494 (f : ℝ → ℝ) (hf : f = λ x => x * (x + 1) * (x + 2) * (x + 3)) :
    (∃ x₀, f x₀ = -1 ∧ ∀ x, f x ≥ -1) ∧
    IsGreatest {y | ∃ x, y = f x ∧ -2 ≤ x ∧ x ≤ -1} (9 / 16) := by 
  have h_eq : ∀ x, f x = x * (x + 1) * (x + 2) * (x + 3) := by
    intro x
    rw [hf]
  constructor
  · -- First part: minimum value is -1.
    use (-3 + Real.sqrt 5) / 2
    constructor
    · -- Show f((-3 + Real.sqrt 5) / 2) = -1
      have eq1 : (f ((-3 + Real.sqrt 5) / 2 : ℝ) ) = -1 := by
        rw [h_eq]
        nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), mul_pos (show 0 < Real.sqrt 5 by positivity) (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
      linarith
    · -- Show ∀ x, f x ≥ -1
      have eq2 : ∀ (x : ℝ), f x ≥ -1 := by
        intro x
        have eq3 : (f x : ℝ) = x * (x + 1) * (x + 2) * (x + 3) := h_eq x
        rw [eq3]
        nlinarith [sq_nonneg (x ^ 2 + 3 * x + 1), sq_nonneg (x * (x + 3) + 1), sq_nonneg ((x + 1) * (x + 2) - 1), sq_nonneg (x + 3 / 2), sq_nonneg (x * (x + 1) -1 ), sq_nonneg ((x + 2) * (x + 3) - 1), sq_nonneg ((x + 1) * (x + 2) - 1)]
      intro x
      apply eq2 x
  · -- Show 9/16 is greatest
    constructor
    · -- Show that 9/16 is inside the image of f over the interval
      use (-3 / 2 : ℝ)
      constructor
      · -- Show that 9/16 = f (-3/2)
        rw [h_eq]
        norm_num
      constructor
      · norm_num
      · norm_num
    · -- Show that 9/16 is the greatest
      intro y hy
      rcases hy with ⟨x, hfx, hx1, hx2⟩
      rw [h_eq x] at hfx
      nlinarith [sq_nonneg (x + 3/2), sq_nonneg ((x +1/2)*(x+ 3/2)), sq_nonneg ((x + 3/2) * (x + -3/2)), sq_nonneg ((x+1) * (x+2)), sq_nonneg ((x * (x + 3))), sq_nonneg ((x+1)*(x+2)), sq_nonneg ((x+1/2)), sq_nonneg ((x+ 3/2))]