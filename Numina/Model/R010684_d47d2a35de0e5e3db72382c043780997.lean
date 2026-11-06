import Mathlib

theorem algebra_20306 {a b : ℝ} (p : ℝ → ℝ) (hp: p = fun x => x ^ 2 + a * x + b) (h : 2 * a ≠ b) (h1 : p (2 * a) = 0)
    (h2 : p b = 0) : a + b = -1 := by
  have eq1 : (2 * a) ^ 2 + a * (2 * a) + b = 0 := by 
    rw [hp] at h1
    simpa using h1
  have hb : b = -6 * a^2 := by
    nlinarith 
  have eq2 : b^2 + a * b + b = 0 := by 
    rw [hp] at h2
    simpa using h2
  rw [hb] at eq2
  have h_eq : 6 * a^2 * (6 * a^2 - a - 1) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h_eq) with
  | inl h1 =>
    have ha : a = 0 := by
      nlinarith 
    have hb' : b = 0 := by
      rw [ha] at hb
      nlinarith
    have h_eq : 2 * a = b := by
      rw [ha, hb']
      all_goals norm_num
    contradiction
  | inr h2 =>
    have h3 : 6 * a^2 - a - 1 = 0 := by 
      linarith 
    have h4 : (a - 1/2) * (6 * a + 2) = 0 := by
      nlinarith 
    cases (mul_eq_zero.mp h4) with
    | inl h5 =>
      have ha : a = 1/2 := by
        linarith 
      have hb' : b = -3/2 := by
        rw [ha] at hb
        nlinarith 
      linarith [ha, hb']
    | inr h6 =>
      have ha : a = -1/3 := by
        linarith 
      have hb' : b = -2/3 := by
        rw [ha] at hb
        nlinarith 
      have h_eq : 2 * a = b := by 
        rw [ha, hb']
        all_goals norm_num
      contradiction