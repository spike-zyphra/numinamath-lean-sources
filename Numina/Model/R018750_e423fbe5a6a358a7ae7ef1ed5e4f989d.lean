import Mathlib

open Real Set

theorem algebra_10599 (f : ℝ → ℝ) (hf : f = fun x => x + sqrt (1 - x ^ 2)) :
    IsGreatest {y | ∃ x, y = f x ∧ -1 ≤ x ∧ x ≤ 1} (sqrt 2) := by
  constructor
  · -- Show sqrt 2 is in the image
    use Real.sqrt 2 / 2
    have h1 : sqrt 2 ≥ 0 := by positivity
    have h3 : (Real.sqrt 2 / 2 : ℝ) ≥ -1 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h4 : (Real.sqrt 2 / 2 : ℝ) ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h5 : (1 - (Real.sqrt 2 / 2 : ℝ) ^ 2 : ℝ) = (1 / 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show that f (sqrt 2 / 2) = sqrt 2
      rw [hf]
      have h6 : sqrt (1 - (Real.sqrt 2 / 2 : ℝ) ^ 2) = Real.sqrt 2 / 2 := by
        rw [h5]
        have h7 : sqrt ((1 / 2 : ℝ)) = Real.sqrt 2 / 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        linarith
      simp [h6]
      <;> nlinarith
    constructor
    · exact h3
    · exact h4
  · -- Show that sqrt 2 is greatest
    intro y hy
    rcases hy with ⟨x, h_eq, hx1, hx2⟩
    rw [h_eq, hf]
    have h7 : (x + sqrt (1 - x ^ 2) : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [sq_nonneg (x - Real.sqrt 2 / 2), sq_nonneg (sqrt (1 - x ^ 2) - Real.sqrt 2 / 2),
        Real.sqrt_nonneg (1 - x ^ 2), Real.sqrt_nonneg (2 : ℝ),
        Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x ^ 2 : ℝ) by nlinarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        sq_nonneg (x ^ 2 - (1 - x ^ 2)), 
        Real.sqrt_nonneg (2 : ℝ), 
        mul_nonneg (Real.sqrt_nonneg (1 - x ^ 2)) (Real.sqrt_nonneg (2 : ℝ)), 
        Real.sqrt_le_sqrt (show (1 - x ^ 2 : ℝ) ≤ (1 : ℝ) by nlinarith)
        ]
    simpa using h7