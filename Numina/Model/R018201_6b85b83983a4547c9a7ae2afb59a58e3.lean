import Mathlib

theorem algebra_100549 (x : ℝ) (hx : x^4 - 16 * x - 12 = 0) (hx1 : ∀ x' : ℝ, x'^4 - 16 * x' - 12 = 0 → x' ≤ x) :
    ⌊10 * x⌋ = 27 := by

  have h1 : (x^2 - 2 * x - 2) * (x^2 + 2 * x + 6) = 0 := by
    nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (x + 1), sq_nonneg (x^2 - 4), sq_nonneg (x - 1)]
  
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where $x^2 - 2x - 2 = 0$
    have eq1 : x^2 - 2 * x - 2 = 0 := h2
    have eq2 : x = 1 + Real.sqrt 3 := by
      have eq3 : (x - (1 + Real.sqrt 3)) * (x - (1 - Real.sqrt 3)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - 1)]
      cases' (mul_eq_zero.mp eq3) with eq4 eq5
      · -- If x = 1 + sqrt 3, we're done
        linarith
      · -- If x = 1 - sqrt 3, which is smaller, so not the largest
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg ((1 : ℝ) + Real.sqrt 3 - 1), sq_nonneg ((1 : ℝ) + Real.sqrt 3 - x), hx1 (1 + Real.sqrt 3) (by
          -- Show that (1 + Real.sqrt 3)^4 - 16 * (1 + Real.sqrt 3) - 12 = 0
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg ((1 : ℝ) + Real.sqrt 3 - 1), sq_nonneg ((1 : ℝ) + Real.sqrt 3), sq_nonneg ((1 : ℝ) + Real.sqrt 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        )]
    rw [eq2]
    have h7 : Real.sqrt 3 ≥ 1.732 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - 1.732)]
    have h8 : Real.sqrt 3 ≤ 1.733 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - 1.733)]
    have h4 : ⌊10 * (1 + Real.sqrt 3)⌋ = 27 := by
      have h5 : 27 ≤ 10 * (1 + Real.sqrt 3) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h7]
      have h6 : 10 * (1 + Real.sqrt 3) < (28 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h8]
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith
    exact h4
  · -- Case where $x^2 + 2 x + 6 = 0$
    have h4 : x^2 + 2 * x + 6 > 0 := by
      nlinarith [sq_nonneg (x + 1)]
    nlinarith [sq_nonneg (x + 1)]