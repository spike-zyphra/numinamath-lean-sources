import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_313760 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (sqrt 3 * x + 1) / sqrt (x^2 + 1) + 2) :
  IsGreatest (range f) 4 := by
  constructor
  · -- Show that 4 is attained by f, so it is in the range
    use Real.sqrt 3
    have h1 : Real.sqrt 3 ^ 2 = 3 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    have h2 : sqrt (Real.sqrt 3 ^ 2 + 1) = 2 := by
      rw [show Real.sqrt 3 ^ 2 + 1 = (4 : ℝ) by
        have h1 : Real.sqrt 3 ^ 2 = 3 := by
          exact Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        linarith [h1]
      ]
      have h4 : sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      exact h4
    rw [h₀]
    rw [h2]
    have h3 : sqrt 3 * Real.sqrt 3 = 3 := by
      have h1 : Real.sqrt 3 ^ 2 = 3 := by
        exact Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      linarith [h1]
    field_simp [h3]
    <;> linarith [Real.sqrt_nonneg 3]
  · -- Show that 4 is an upper bound of the range
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h₀] at hx
    have h1 : sqrt (x ^ 2 + 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h4 : ((sqrt 3) * x + 1) / sqrt (x^2 + 1) ≤ 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (x ^ 2 + 1), 
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + 1 : ℝ) by positivity), 
        sq_nonneg (x - Real.sqrt 3), 
        Real.sqrt_nonneg 3 
      ]
    have h5 : ((sqrt 3 * x + 1) / sqrt (x^2 + 1) + 2) ≤ (4 : ℝ) := by
      linarith [h4]
    linarith [hx, h5]