import Mathlib

theorem number_theory_297844 (a b : ℕ → ℤ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (h : ∀ n, (1 + Real.sqrt 3) ^ (2 * n) = a n + Real.sqrt 3 * b n) :
    ∀ n, 2 ^ n ∣ a n ∧ 2 ^ n ∣ b n := by

  have h1 := h 0
  have h2 : (1 + Real.sqrt 3) ^ (2 * (0 : ℕ)) = a 0 + Real.sqrt 3 * b 0 := by
    simpa using h1

  have h3 : (1 + Real.sqrt 3) ^ (2 * (0 : ℕ)) = 1 := by
    norm_num

  rw [h3] at h2

  have h4 : 0 < a 0 := ha 0
  have h5 : 0 < b 0 := hb 0

  have eq1 : (a 0 : ℝ) + Real.sqrt 3 * (b 0 : ℝ) = 1 := by linarith

  -- Derive a contradiction from the existence of positive integers satisfying the equation
  have eq2 : (a 0 : ℝ) > (0 : ℝ) := by
    exact_mod_cast h4
  have eq3 : (b 0 : ℝ) > (0 : ℝ) := by
    exact_mod_cast h5
  -- Expand the equation using the fact about sqrt(3).
  have h6 : (a 0 : ℝ) < 1 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), eq1, eq3]

  have h7 : (a 0 : ℤ) < 1 := by
    exact_mod_cast h6

  omega