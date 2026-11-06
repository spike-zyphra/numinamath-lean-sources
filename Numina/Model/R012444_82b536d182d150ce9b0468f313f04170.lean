import Mathlib

theorem algebra_4439 {a : ℝ} (ha : a^2 + a - 1/4 = 0) : (a^3 - 1)/(a^5 + a^4 - a^3 - a^2) = 20 := by
  have h1 : a^2 = -a + 1/4 := by linarith 
  have h2 : a^3 = 5/4 * a - 1/4 := by
    calc
      a^3 = a * a^2 := by ring 
      _ = a * (-a + 1/4) := by rw [h1]
      _ = -a^2 + 1/4 * a := by ring
      _ = -(-a + 1/4) + 1/4 * a := by rw [h1]
      _ = 5/4 * a - 1/4 := by ring
  have h3 : a^4 = -3/2 * a + 5/16 := by
    calc
      a^4 = (a^2)^2 := by ring
      _ = (-a + 1/4)^2 := by rw [h1]
      _ = a^2 - (1/2) * a + 1/16 := by ring
      _ = (-a + 1/4) - (1/2) * a + 1/16 := by rw [h1]
      _ = -3/2 * a + 5/16 := by ring
  have h4 : a^5 = 29/16 * a - 6/16 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (-3/2 * a + 5/16) := by rw [h3]
      _ = -3/2 * a^2 + 5/16 * a := by ring
      _ = -3/2 * (-a + 1/4) + 5/16 * a := by rw [h1]
      _ = 29/16 * a - 6/16 := by ring
  have h5 : a^3 - 1 = 5/4 * (a - 1) := by 
    rw [h2]
    ring
  have h6 : a^5 + a^4 - a^3 - a^2 = 1/16 * (a - 1) := by 
    rw [h4, h3, h2, h1]
    ring_nf
  have h7 : a - 1 ≠ 0 := by 
    by_contra h
    have ha1 : a = 1 := by linarith 
    rw [ha1] at ha 
    norm_num at ha 
  have h8 : (a^3 - 1) / (a^5 + a^4 - a^3 - a^2) = 20 := by 
    rw [h5, h6]
    have h9 : (5/4 * (a - 1) ) / (1/16 * (a - 1)) = 20 := by
      have h10 : a - 1 ≠ 0 := h7
      field_simp [h10]
      <;> linarith
    linarith [h9]
  exact h8