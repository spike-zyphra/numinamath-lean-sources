import Mathlib

theorem algebra_300330 (f : ℝ → ℝ) (hf : f = fun x => x^2 - abs (2 * x - 1) - 4) :
    ∑ᶠ x ∈ {x | f x = 0}, x = 2 - Real.sqrt 6 := by

  have h1 : {x | f x = 0} = {3, -1 - Real.sqrt 6} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f(x) = 0, prove x ∈ {3, -1 - Real.sqrt 6}
      intro hx
      by_cases h : (2 * x - 1) ≥ 0
      · -- If $2x - 1 ≥ 0$, then $|2x - 1| = 2x - 1$.
        have h2 : abs (2 * x - 1) = (2 * x - 1 : ℝ) := by
          rw [abs_of_nonneg]
          linarith
        rw [h2] at hx
        have h3 : x^2 - (2 * x - 1) - 4 = 0 := by linarith
        have h4 : (x - 3) * (x + 1) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h4) with h5 h6
        · -- x - 3 = 0
          left
          linarith
        · -- x + 1 = 0
          exfalso
          nlinarith
      · -- If $2x - 1 < 0$.
        have h2 : abs (2 * x - 1) = -(2 * x - 1 : ℝ) := by
          rw [abs_of_neg]
          linarith
        rw [h2] at hx
        have h5 : x^2 + 2 * x - 5 = 0 := by
          nlinarith
        have h6 : (x - (-1 + Real.sqrt 6)) * (x - (-1 - Real.sqrt 6)) = 0 := by
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h6) with h7 h8
        · -- Let's prove the roots doesn't hold here
          exfalso
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
        · -- Let's prove the roots match here
          right
          linarith
    · -- Assume x ∈ {3, -1 - Real.sqrt 6}, prove f(x) = 0.
      rintro (rfl | rfl)
      · -- x = 3
        norm_num [abs_of_nonneg]
      · -- x = -1 - Real.sqrt 6
        have h1 : (2 * (-1 - Real.sqrt 6) - 1 : ℝ) < 0 := by
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
        have h2 : abs (2 * (-1 - Real.sqrt 6) - 1 : ℝ) = - (2 * (-1 - Real.sqrt 6) - 1 : ℝ) := by
          rw [abs_of_neg]
          linarith
        rw [h2]
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]

  rw [h1]
  rw [finsum_mem_pair (by
    -- Show 3 ≠ -1 - Real.sqrt 6
    intro h
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  )]
  all_goals
  nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]