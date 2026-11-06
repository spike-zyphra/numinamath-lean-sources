import Mathlib

theorem algebra_325814 {a : ℝ} (ha : a^2 + a - 1 / 4 = 0) :
    (a^3 - 1) / (a^5 + a^4 - a^3 - a^2) = 20 := by

  have ha2 : a^2 = -a + 1 / 4 := by linarith 
  have ha3 : a^3 = 5 / 4 * a - 1 / 4 := by 
    calc
      a^3 = a * a^2 := by ring
      _ = a * (-a + 1 / 4) := by rw [ha2]
      _ = -a^2 + (1 / 4) * a := by ring
      _ = -(-a + 1 / 4) + (1 / 4) * a := by rw [ha2]
      _ = 5 / 4 * a - 1 / 4 := by ring
  
  have ha4 : a^4 = -3 / 2 * a + 5 / 16 := by 
    calc
      a^4 = (a^2)^2 := by ring
      _ = (-a + 1 / 4)^2 := by rw [ha2]
      _ = a^2 - (1 / 2) * a + 1 / 16 := by ring
      _ = (-a + 1 / 4) - (1 / 2) * a + 1 / 16 := by rw [ha2]
      _ = -3 / 2 * a + 5 / 16 := by ring
  
  have ha5 : a^5 = 29 / 16 * a - 3 / 8 := by 
    calc
      a^5 = a * a^4 := by ring
      _ = a * (-3 / 2 * a + 5 / 16) := by rw [ha4]
      _ = -3 / 2 * a^2 + 5 / 16 * a := by ring
      _ = -3 / 2 * (-a + 1 / 4) + 5 / 16 * a := by rw [ha2]
      _ = 29 / 16 * a - 3 / 8 := by ring
  
  have denom_eq : a^5 + a^4 - a^3 - a^2 = (a - 1) / 16 := by 
    rw [ha5, ha4, ha3, ha2]
    linarith
  
  have num_eq : a^3 - 1 = 5 / 4 * (a - 1) := by 
    linarith [ha3]

  have h1 : a^5 + a^4 - a^3 - a^2 = (a - 1) / 16 := by 
    exact denom_eq
  
  -- Show that a - 1 ≠ 0
  have h2 : a - 1 ≠ 0 := by
    by_contra h
    have h_eq : a = 1 := by linarith 
    rw [h_eq] at ha 
    norm_num at ha
  
  -- Show denominator is not zero.
  have h3 : a^5 + a^4 - a^3 - a^2 ≠ 0 := by
    by_contra h_eq
    have h_zero : (a - 1) / 16 = 0 := by
      linarith [denom_eq, h_eq]
    have h_zero1 : a - 1 = 0 := by
      linarith [h_zero]
    exfalso 
    apply h2
    linarith [h_zero1]

  rw [num_eq, denom_eq]
  field_simp [show a - 1 ≠ 0 by exact h2]
  <;> linarith