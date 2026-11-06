import Mathlib

theorem algebra_132449 (n : ℕ) (hn : n ≤ 24) (h : n * 1 + (24 - n) * (-1 / 4 : ℝ) = 13) :
    n ≤ 15 := by 
  by_contra h2
  push_neg at h2
  have h3 : (n : ℝ) ≥ 16 := by 
    exact_mod_cast h2
  have h4 : (n : ℝ) * 1 + (24 - (n : ℝ)) * (-1 / 4 : ℝ) = (13 : ℝ) := by
    simpa using h
  -- compute from h4 that (n : ℝ) = 76 / 5
  have h5 : (n : ℝ) = 76 / 5 := by
    linarith
  -- simplify h5
  -- show contradiction of h5 with a fact that n : ℕ
  have h9 : (5 * (n : ℝ) : ℝ) = 76 := by 
    linarith
  -- rewrite 5 * (n : ℝ) to a real number 5 * n, and derive 5 * n = 76 (in ℕ question)
  have h14 : (5 * (n : ℝ)) = (76 : ℝ) := h9
  -- convert from equation of reals to equation of ℕ
  have h15 : 5 * n = 76 := by
    exact_mod_cast h14
  omega