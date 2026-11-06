import Mathlib

theorem algebra_13820 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : a / b + b / a = 5) (h2 : a ^ 2 / b + b ^ 2 / a = 12) :
    1 / a + 1 / b = 7 / 3 := by 
  have eq1 : a^2 + b^2 = 5 * (a * b) := by
    field_simp [ha, hb] at h1
    linarith
  have eq2 : a^3 + b^3 = 12 * (a * b) := by 
    field_simp [ha, hb] at h2
    ring_nf at h2 ⊢
    linarith 
  have eq3 : a^3 + b^3 = (a + b)^3 - 3 * (a * b) * (a + b) := by 
    ring 
  have eq4 : (a + b)^2 = 7 * (a * b) := by
    have h_eq : a^2 + b^2 = 5 * (a * b) := eq1 
    have h_eq5 : (a + b)^2 = a^2 + 2 * (a * b) + b^2 := by 
      ring 
    have h_eq6 : (a + b)^2 = 7 * (a * b) := by 
      have eq2 : a^2 + b^2 = 5 * (a * b) := h_eq
      linarith [h_eq5, eq2]
    exact h_eq6 
  have eq5 : a + b = 3 := by 
    have eq6 : (a + b)^3 - 3 * (a * b) * (a + b) = 12 * (a * b) := by 
      linarith [eq2, eq3] 
    have eq7 : (a + b)^3 = 7 * (a * b) * (a + b) := by 
      have h_eq : (a + b)^2 = 7 * (a * b) := eq4 
      calc 
        (a + b)^3 = (a + b) * (a + b)^2 := by ring 
        _ = (a + b) * (7 * (a * b)) := by rw [h_eq] 
        _ = 7 * (a * b) * (a + b) := by ring 
    rw [eq7] at eq6 
    have h4 : a * b ≠ 0 := by 
      apply mul_ne_zero 
      exact ha 
      exact hb 
    have eq8 : 4 * (a * b) * (a + b) - 12 * (a * b) = 0 := by 
      nlinarith 
    have eq9 : (a + b) - 3 = 0 := by 
      have h5 : 4 * (a * b) * ((a + b) - 3) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h5) with h6 h7 
      · 
        have h8 : a * b = 0 := by 
          nlinarith 
        have h9 : a * b = 0 := by 
          linarith 
        cases' (mul_eq_zero.mp h9) with h10 h11 
        · 
          contradiction 
        · 
          contradiction 
      · 
        linarith 
    linarith 
  have eq10 : a * b = 9 / 7 := by 
    have eq4' : (a + b)^2 = 7 * (a * b) := eq4 
    rw [show (a + b) = 3 by linarith [eq5] ] at eq4' 
    nlinarith 
  have eq11 : 1 / a + 1 / b = (a + b) / (a * b) := by 
    field_simp [ha, hb] 
    <;> ring 
  rw [eq11] 
  rw [show (a + b) = 3 by linarith [eq5]]
  rw [show (a * b) = 9 / 7 by linarith [eq10]]
  all_goals norm_num