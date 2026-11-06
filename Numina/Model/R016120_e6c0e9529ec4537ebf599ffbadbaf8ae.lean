import Mathlib

theorem algebra_259941 (c : ℝ) (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x^3 + 3 * x^2 + 6 * x + c = 0 ∧
    y^3 + 3 * y^2 + 6 * y + c = 0 ∧ z^3 + 3 * z^2 + 6 * z + c = 0 ∧ ∃ r, y = x * r ∧ z = y * r) :
    c = 8 := by 
  rcases h with ⟨x, y, z, h1, h2, h3, h4, h5, h6, r, h7, h8⟩
  -- Equation derived from h4 and h5 by eliminating c 
  have eq1 : y^2 + y * x + x^2 + 3 * (y + x) + 6 = 0 := by 
    have eq2 : y^3 + 3 * y^2 + 6 * y + c = 0 := h5
    have eq3 : x^3 + 3 * x^2 + 6 * x + c = 0 := h4
    have eq4 : y^3 + 3 * y^2 + 6 * y + c - (x^3 + 3 * x^2 + 6 * x + c) = 0 := by 
      linarith
    have eq5 : y - x ≠ 0 := by
      intro h0
      have : y = x := by linarith 
      tauto 
    have eq1' : (y - x) * (y^2 + y * x + x^2 + 3 * (y + x) + 6) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (y - x : ℝ) ≠ 0 by exact eq5)]
    cases' (mul_eq_zero.mp eq1') with h7 h8
    · -- y - x = 0
      exfalso 
      tauto 
    · -- the quadratic factor is zero 
      linarith 
  -- Equation derived from h5 and h6 by eliminating c 
  have eq2 : z^2 + z * y + y^2 + 3 * (z + y) + 6 = 0 := by 
    have eq7 : z^3 + 3 * z^2 + 6 * z + c = 0 := h6 
    have eq8 : y^3 + 3 * y^2 + 6 * y + c = 0 := h5
    have eq9 : z^3 + 3 * z^2 + 6 * z + c - (y^3 + 3 * y^2 + 6 * y + c) = 0 := by 
      linarith
    have eq5' : z - y ≠ 0 := by
      intro h0
      have : z = y := by linarith 
      tauto 
    have eq13 : (z - y) * (z^2 + z * y + y^2 + 3 * (z + y) + 6) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (z - y : ℝ) ≠ 0 by exact eq5')]
    cases' (mul_eq_zero.mp eq13) with h7 h8
    · -- z - y = 0
      exfalso 
      tauto 
    · -- the quadratic factor is zero 
      linarith 
  -- Equation obtained by substituting y = x*r into eq1
  have eq3 : x^2 * (r^2 + r + 1) + 3 * x * (r + 1) + 6 = 0 := by
    rw [show y = x * r by linarith [h7]] at eq1 
    nlinarith 
  -- Equation obtained by substituting z = y*r and y = x*r into eq2
  have h9 : z = x * r^2 := by
    have h10 : z = y * r := by linarith [h8] 
    rw [show y = x * r by linarith [h7]] at h10 
    nlinarith 
  have eq4 : x^2 * r^4 + x^2 * r^3 + x^2 * r^2 + 3 * x * r^2 + 3 * x * r + 6 = 0 := by 
    rw [show z = x * r^2 by linarith [h9], show y = x * r by linarith [h7]] at eq2 
    nlinarith 
  have hx : x ≠ 0 := by 
    by_contra h0
    have h4' : x = 0 := by linarith 
    have h7' : y = 0 := by 
      nlinarith [h7, h4']
    have h8' : z = 0 := by
      nlinarith [h8, h7', h4']
    have h1' : x = y := by
      linarith [h4', h7']
    tauto 
  have hc : c = -x^3 - 3*x^2 - 6*x := by 
    nlinarith 
  -- Solving the equations to get c = 8 
  nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show r - 1 ≠ 0 by 
    by_contra h0
    have h10 : r = 1 := by linarith 
    have h11 : y = x := by 
      nlinarith [h7, h10]
    tauto 
  ), sq_nonneg (x + 2), sq_nonneg (r + 1), sq_nonneg (x * r + 2), sq_nonneg ((x * r) * r + 2)]