import Mathlib

theorem number_theory_600602 (n : ℝ) (hn : n > 0) :
    133^5 + 110^5 + 84^5 + 27^5 = n^5 ↔ n = 144 := by 
  constructor
  · -- Assume 133^5 + 110^5 + 84^5 + 27^5 = n^5, prove n = 144
    intro h
    have h1 : n^5 = (133 : ℝ) ^ 5 + (110 : ℝ) ^ 5 + (84 : ℝ) ^ 5 + (27 : ℝ) ^ 5 := by linarith
    have h5 : n^5 = (144 : ℝ) ^ 5 := by
      nlinarith [h1]
    have h6 : n = (144 : ℝ) := by
      have h7 : n^5 - (144 : ℝ) ^ 5 = 0 := by linarith
      have h8 : (n - 144 : ℝ) * (n^4 + n^3 * 144 + n^2 * 144^2 + n * 144^3 + 144^4) = 0 := by
        nlinarith [h7]
      cases' (mul_eq_zero.1 h8) with h9 h10
      · 
        linarith [h9]
      · 
        have h11 : n^4 + n^3 * 144 + n^2 * 144^2 + n * 144^3 + 144^4 > 0 := by
          nlinarith [sq_nonneg (n^2), sq_nonneg (n + 144 / 2), sq_nonneg (n^2 - 144^2 / 4), sq_nonneg (n * 144), sq_nonneg (n - 144), sq_nonneg (n + 144), hn]
        linarith [h10, h11]
    linarith
  · -- Assume n = 144, prove 133^5 + 110^5 + 84^5 + 27^5 = n^5
    intro h
    rw [show n = (144 : ℝ) by linarith [h]]
    nlinarith