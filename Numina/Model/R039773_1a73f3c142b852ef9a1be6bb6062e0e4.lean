import Mathlib

theorem algebra_246584 (n : ℕ) (h : n > 0) :
    (1 / (n * (n + 1)) : ℝ) < (1 / n ^ 2 : ℝ) := by
  have h1 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast h
  have h2 : (n * (n + 1) : ℝ) > (0 : ℝ) := by
    have hn1 : (n : ℝ) > 0 := by exact_mod_cast h
    have hn2 : (n + 1 : ℝ) > 0 := by
      nlinarith
    nlinarith [hn1, hn2, mul_pos hn1 hn2]
  have h3 : (n ^ 2 : ℝ) > (0 : ℝ) := by
    have hn1 : (n : ℝ) > 0 := by exact_mod_cast h
    nlinarith [sq_pos_of_pos hn1, sq_nonneg (n : ℝ)]
  have h4 : (n ^ 2 : ℝ) < (n * (n + 1) : ℝ) := by
    have hn1 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast h
    nlinarith [sq_pos_of_pos hn1, sq_nonneg ((n : ℝ) - 1)]
  have h5 : (1 / (n * (n + 1)) : ℝ) < (1 / n ^ 2 : ℝ) := by
    apply (one_div_lt_one_div (by positivity) (by positivity)).mpr
    nlinarith [h4, sq_pos_of_pos h1, mul_pos h1 (show (n + 1 : ℝ) > 0 by nlinarith)]
  exact h5