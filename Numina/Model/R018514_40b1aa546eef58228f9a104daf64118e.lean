import Mathlib

theorem algebra_276601 {p q a : ℝ} (h : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧ |x - y| = a) :
    a^2 - p^2 = -4 * q := by
  rcases h with ⟨x, y, hxy, hx, hy, habs⟩
  have h1 : (x - y) ^ 2 = a ^ 2 := by
    have h2 : |x - y| = a := habs
    cases' abs_cases (x - y) with h3 h3
    · -- Case where x - y ≥ 0
      nlinarith
    · -- Case where x - y < 0
      nlinarith
  have h2 : x + y = -p := by
    have h3 : (x - y) * (x + y) + p * (x - y) = 0 := by 
      nlinarith 
    have h4 : x - y ≠ 0 := by
      intro h 
      apply hxy 
      linarith 
    have h5 : x + y + p = 0 := by 
      apply (mul_left_inj' h4).mp 
      linarith 
    linarith 
  -- Prove x*y = q 
  have h_eq5 : x * y = q := by 
    have h_eq6 : x + y = -p := h2 
    have eq1 : x^2 + p * x + q = 0 := hx 
    have eq2 : y^2 + p * y + q = 0 := hy 
    have eq3 : x^2 + p * x + q + (y^2 + p * y + q) = 0 := by 
      linarith 
    have eq4 : x^2 + y^2 + p * (x + y) + 2 * q = 0 := by 
      nlinarith 
    have eq5 : x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by 
      nlinarith 
    rw [show (x + y) = -p by linarith [h_eq6]] at eq5 
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by 
      intro h 
      apply hxy 
      linarith 
    )]
  -- Prove (x - y)^2 = p^2 - 4q 
  have h4 : (x - y) ^ 2 = p ^ 2 - 4 * q := by 
    have h5 : x + y = -p := h2 
    have h6 : x * y = q := h_eq5 
    have h7 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by 
      nlinarith 
    rw [h6] at h7 
    rw [show (x + y) = -p by linarith [h5]] at h7 
    nlinarith 
  nlinarith [h1, h4]