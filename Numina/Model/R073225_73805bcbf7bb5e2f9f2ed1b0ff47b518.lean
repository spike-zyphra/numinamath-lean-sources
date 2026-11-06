import Mathlib

theorem algebra_31356 (a b : ℝ) : ¬(2*a*b=6*(a+b)-13 ∧ a^2+b^2=4) := by
  rintro ⟨h1, h2⟩
  have h3 : (a + b) ^ 2 = 6 * (a + b) - 9 := by
    have h4 : (a + b) ^ 2 = a^2 + b^2 + 2 * (a * b) := by ring
    rw [h2] at h4
    have h5 : 2 * (a * b) = 6 * (a + b) - 13 := by 
      nlinarith 
    nlinarith [h4, h5]
  have h6 : (a + b - 3) ^ 2 = 0 := by 
    nlinarith 
  have hab : a + b = 3 := by 
    nlinarith [pow_eq_zero h6] 
  have hab2 : a * b = 5 / 2 := by 
    have h7 : 2 * (a * b) = 6 * (a + b) - 13 := by 
      nlinarith 
    rw [hab] at h7 
    nlinarith 
  have h7 : (a - b) ^ 2 ≥ 0 := by 
    nlinarith 
  have h8 : (a - b) ^ 2 = -1 := by 
    nlinarith [hab, hab2] 
  linarith