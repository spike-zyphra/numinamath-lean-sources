import Mathlib

theorem algebra_165336 {a r : ℝ} (ha : a = 7 - 3 * Real.sqrt 5) (hr : r > 0)
    (h : ∀ n, a * r ^ (n + 1) = a * r ^ n - a * r ^ (n - 1)) :
    a * r ^ 4 = 2 := by
  have eq1 := h 0
  have eq2 : a * r = (0 : ℝ) := by
    have eq3 := h 0
    have eq4 : a * r ^ (0 + 1) = a * r ^ 0 - a * r ^ (0 - 1 : ℕ) := by 
      simpa using eq3
    have eq5 : a * r ^ (0 + 1) = a * r := by
      simp [pow_succ, pow_zero]
    have eq6 : a * r ^ (0 - 1 : ℕ) = a := by
      have h1 : (0 - 1 : ℕ) = 0 := by 
        omega 
      rw [h1]
      have h2 : a * r ^ (0 : ℕ) = a := by 
        simp 
      linarith [h2]
    have eq7 : a * r ^ 0 = a := by 
      simp 
    simp [eq5, eq6] at eq4 
    linarith 
  have ha1 : a ≠ 0 := by 
    rw [ha]
    by_contra h
    have : Real.sqrt 5 = (7 / 3 : ℝ) := by 
      nlinarith 
    have h1 : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
    rw [this] at h1 
    nlinarith 
  -- We have `a * r = 0` and `a ≠ 0`. Thus `r = 0`.
  have eq4 : r = (0 : ℝ) := by 
    apply (mul_left_inj' ha1).mp 
    linarith [eq2]
  -- This contradicts `hr : r > 0`. 
  nlinarith [eq4, hr]