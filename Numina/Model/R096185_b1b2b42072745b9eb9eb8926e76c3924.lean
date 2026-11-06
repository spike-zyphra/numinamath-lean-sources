import Mathlib

theorem algebra_40867 {a b : ℝ} (h1 : a^2 + b^2 = 25) (h2 : 3 * (a + b) - a * b = 15) :
    (a, b) = (0, 5) ∨ (a, b) = (5, 0) ∨ (a, b) = (4, -3) ∨ (a, b) = (-3, 4) := by

  have h3 : (a + b) ^ 2 = 25 + 2 * (a * b) := by
    nlinarith
  
  have h4 : a * b = 3 * (a + b) - 15 := by
    linarith
  
  have h5 : (a + b) ^ 2 - 6 * (a + b) + 5 = 0 := by
    rw [h4] at h3
    nlinarith
  
  have h6 : ((a + b) - 1) * ((a + b) - 5) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.1 h6) with h7 h8
  
  · -- Case where a + b = 1
    have h10 : a + b = 1 := by linarith
    have h11 : a * b = -12 := by
      nlinarith [h1, h10]
    have h12 : (a - 4) * (a + 3) = 0 := by
      nlinarith [h10, h11]
    cases' (mul_eq_zero.1 h12) with ha1 ha2
    · -- Case where a = 4
      have ha : a = 4 := by linarith
      have hb : b = -3 := by
        nlinarith
      simp [ha, hb]
      <;> linarith
    · -- Case where a = -3
      have ha : a = -3 := by linarith
      have hb : b = 4 := by
        nlinarith
      simp [ha, hb]
      <;> linarith

  · -- Case where a + b = 5
    have h10 : a + b = 5 := by linarith
    have h11 : a * b = 0 := by
      nlinarith [h1, h10]
    cases' (mul_eq_zero.1 h11) with ha1 ha2
    · -- Case where a = 0
      have ha : a = 0 := by linarith
      have hb : b = 5 := by
        nlinarith
      simp [ha, hb]
      <;> linarith
    · -- Case where b = 0
      have hb : b = 0 := by linarith
      have ha : a = 5 := by
        nlinarith
      simp [ha, hb]
      <;> linarith