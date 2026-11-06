import Mathlib

theorem algebra_124305 {a b : ℝ} (ha : a^4 + a^3 - 1 = 0) (hb : b^4 + b^3 - 1 = 0)
    (hab : a ≠ b) :
    (a * b)^6 + (a * b)^4 + (a * b)^3 - (a * b)^2 - 1 = 0 := by 
  have h1 : a^4 + a^3 - 1 - (b^4 + b^3 - 1) = 0 := by
    have ha1 : a^4 + a^3 - 1 = 0 := ha
    have hb1 : b^4 + b^3 - 1 = 0 := hb
    linarith
  have h2 : a^4 - b^4 + a^3 - b^3 = 0 := by 
    linarith [h1]
  have h3 : (a - b) * (a^3 + a^2 * b + a * b^2 + b^3 + a^2 + a * b + b^2) = 0 := by 
    ring_nf at h2 ⊢ 
    <;> linarith 
  have h4 : a^3 + a^2 * b + a * b^2 + b^3 + a^2 + a * b + b^2 = 0 := by 
    cases' (mul_eq_zero.1 h3) with h5 h6 
    · -- a - b = 0, so a = b, a contradiction 
      exfalso 
      apply hab 
      linarith 
    · -- the polynomial is zero 
      linarith 
  have eq1 : a^4 = 1 - a^3 := by 
    linarith [ha] 
  have eq2 : b^4 = 1 - b^3 := by 
    linarith [hb] 
  have eq3 : a^5 = a - 1 + a^3 := by 
    calc 
      a^5 = a * a^4 := by ring 
      _ = a * (1 - a^3) := by rw [eq1] 
      _ = a - a^4 := by ring 
      _ = a - (1 - a^3) := by rw [eq1] 
      _ = a - 1 + a^3 := by ring 
  have eq4 : a^6 = a^2 - a + 1 - a^3 := by 
    calc 
      a^6 = a * a^5 := by ring 
      _ = a * (a - 1 + a^3) := by rw [eq3] 
      _ = a^2 - a + a^4 := by ring 
      _ = a^2 - a + (1 - a^3) := by rw [eq1] 
      _ = a^2 - a + 1 - a^3 := by ring 
  have eq5 : b^5 = b - 1 + b^3 := by 
    calc 
      b^5 = b * b^4 := by ring 
      _ = b * (1 - b^3) := by rw [eq2] 
      _ = b - b^4 := by ring 
      _ = b - (1 - b^3) := by rw [eq2] 
      _ = b - 1 + b^3 := by ring 
  have eq6 : b^6 = b^2 - b + 1 - b^3 := by 
    calc 
      b^6 = b * b^5 := by ring 
      _ = b * (b - 1 + b^3) := by rw [eq5] 
      _ = b^2 - b + b^4 := by ring 
      _ = b^2 - b + (1 - b^3) := by rw [eq2] 
      _ = b^2 - b + 1 - b^3 := by ring 
  have eq7 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring 
  have eq8 : (a * b) ^ 3 = a ^ 3 * b ^ 3 := by ring 
  have eq9 : (a * b) ^ 4 = a^4 * b^4 := by ring 
  have eq10 : (a * b) ^ 6 = a^6 * b^6 := by ring 
  rw [eq10, eq9, eq8, eq7] 
  rw [show a^4 = 1 - a^3 by linarith [ha], show b^4 = 1 - b^3 by linarith [hb]]
  rw [show a^6 = a^2 - a + 1 - a^3 by linarith [eq4], show b^6 = b^2 - b + 1 - b^3 by linarith [eq6]]
  nlinarith [h4, sq_pos_of_ne_zero (show (a - b) ≠ 0 by 
    by_contra h 
    have : a = b := by linarith 
    tauto 
  )]