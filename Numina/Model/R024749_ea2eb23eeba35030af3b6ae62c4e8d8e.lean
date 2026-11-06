import Mathlib

theorem algebra_182125 {a : ℕ} (ha : a < (1 / (1 / 2011 + 1 / 2012 + 1 / 2013 + 1 / 2014 + 1 / 2015 : ℚ)) ∧ (1 / (1 / 2011 + 1 / 2012 + 1 / 2013 + 1 / 2014 + 1 / 2015 : ℚ)) < a + 1) :
    a = 402 := by
  have h1 : (a : ℚ) < 1 / (1 / 2011 + 1 / 2012 + 1 / 2013 + 1 / 2014 + 1 / 2015 : ℚ) := by
    linarith [ha.1]
  have h2 : (1 / (1 / 2011 + 1 / 2012 + 1 / 2013 + 1 / 2014 + 1 / 2015 : ℚ) : ℚ) < (a + 1 : ℚ) := by
    linarith [ha.2]
  have h3 : a = 402 := by
    have h4 : a < 403 := by
      by_contra h
      push_neg at h
      have h5 : (a : ℚ) ≥ (403 : ℚ) := by
        exact_mod_cast (show (a : ℕ) ≥ (403 : ℕ) by omega)
      nlinarith
    have h6 : a > 401 := by
      by_contra h
      push_neg at h
      have h7 : (a : ℚ) ≤ (401 : ℚ) := by
        exact_mod_cast (show (a : ℕ) ≤ (401 : ℕ) by omega)
      nlinarith
    omega
  exact h3