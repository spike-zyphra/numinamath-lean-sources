import Mathlib

theorem algebra_264988 (a : ℝ) (h : ∃ x y, x ≠ y ∧ x^2 + a * x + a + 1 = 0 ∧ y^2 + a * y + a + 1 = 0 ∧
    x^3 + y^3 = 1) :
    a = -1 := by
  rcases h with ⟨x, y, hxy, hx, hy, hsum⟩
  have h1 : x + y = -a := by
    have h4 : x^2 + a * x + a + 1 = 0 := hx
    have h5 : y^2 + a * y + a + 1 = 0 := hy
    have h4 : x^2 - y^2 + a * (x - y) = 0 := by
      nlinarith
    have h5 : (x - y) * (x + y + a) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- x - y = 0, so x = y, contradicts
      exfalso
      apply hxy
      linarith
    · -- x + y + a = 0, so x + y = -a
      linarith
  have h2 : x * y = a + 1 := by
    have eq3 : y * (x^2 + a * x + a + 1) - x * (y^2 + a * y + a + 1) = 0 := by 
      have eq1 : x^2 + a * x + a + 1 = 0 := hx
      have eq2 : y^2 + a * y + a + 1 = 0 := hy
      calc 
        y * (x^2 + a * x + a + 1) - x * (y^2 + a * y + a + 1)
          = y * (0) - x * (0) := by rw [eq1, eq2]
        _ = (0 : ℝ) := by ring 
    have eq4 : (x - y) * (x * y - (a + 1)) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by intro h8; apply hxy; linarith)]
    cases' (mul_eq_zero.1 eq4) with h7 h8
    · -- x - y = 0, so x = y, which contradicts hxy
      exfalso
      apply hxy
      linarith
    · -- x * y - (a + 1) = 0, so x * y = a + 1
      linarith
  -- Compute x^3 + y^3 using the identity x^3 + y^3 = (x + y)^3 - 3xy(x + y)
  have h3 : x^3 + y^3 = (-a)^3 - 3 * (a + 1) * (-a) := by
    have h7 : x + y = -a := h1
    have h8 : x * y = a + 1 := h2
    have h9 : x^3 + y^3 = (x + y)^3 - 3 * (x * y) * (x + y) := by 
      ring_nf
    rw [h9, h7, h8]
    <;> nlinarith 
  -- Now equate to 1 and solve for a
  rw [h3] at hsum
  have h4 : a ^ 3 - 3 * a ^ 2 - 3 * a + 1 = 0 := by
    nlinarith 
  have h5 : (a + 1) * (a ^ 2 - 4 * a + 1) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- a + 1 = 0, so a = -1
    linarith
  · -- a ^ 2 - 4 * a + 1 = 0 
    have h6 : a ^ 2 - 4 * a + 1 = 0 := by
      linarith 
    nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by intro h8; apply hxy; linarith), sq_nonneg (x - y), sq_nonneg (x + y + 2), sq_nonneg (x * y - (a + 1)), sq_pos_of_pos (show 0 < (x - y) ^ 2 by 
      apply sq_pos_of_ne_zero 
      intro h
      apply hxy
      linarith 
    )]