import Mathlib

theorem algebra_177272 (a b c : ℝ) (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    (x^3 + a * x^2 + b * x + c = 0) ∧ (y^3 + a * y^2 + b * y + c = 0) ∧
    (z^3 + a * z^2 + b * z + c = 0)) : 3 * b ≤ a^2 := by
  rcases h with ⟨x, y, z, hx1, hy1, hz1, h1, h2, h3⟩
  have eq1 : x^2 + x * y + y^2 + a * (x + y) + b = 0 := by
    have h4 : x^3 + a * x^2 + b * x + c = 0 := h1
    have h5 : y^3 + a * y^2 + b * y + c = 0 := h2
    have h6 : x^3 + a * x^2 + b * x + c - (y^3 + a * y^2 + b * y + c) = 0 := by
      linarith 
    have h7 : (x - y) * (x^2 + x * y + y^2 + a * (x + y) + b) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h7) with h8 h9 
    · -- x - y = 0, but x ≠ y 
      exfalso 
      exact hx1 (by linarith) 
    · -- x^2 + x * y + y^2 + a * (x + y) + b = 0 
      linarith

  have eq2 : y^2 + y * z + z^2 + a * (y + z) + b = 0 := by
    have h4 : y^3 + a * y^2 + b * y + c = 0 := h2
    have h5 : z^3 + a * z^2 + b * z + c = 0 := h3
    have h6 : y^3 + a * y^2 + b * y + c - (z^3 + a * z^2 + b * z + c) = 0 := by
      linarith 
    have h7 : (y - z) * (y^2 + y * z + z^2 + a * (y + z) + b) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9 
    · -- y - z = 0, but y ≠ z 
      exfalso 
      exact hy1 (by linarith) 
    · -- y^2 + y * z + z^2 + a * (y + z) + b = 0 
      linarith

  have eq3 : x^2 + x * z + z^2 + a * (x + z) + b = 0 := by
    have h4 : x^3 + a * x^2 + b * x + c = 0 := h1
    have h5 : z^3 + a * z^2 + b * z + c = 0 := h3
    have h6 : x^3 + a * x^2 + b * x + c - (z^3 + a * z^2 + b * z + c) = 0 := by
      linarith
    have h7 : (x - z) * (x^2 + x * z + z^2 + a * (x + z) + b) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- x - z = 0, but z ≠ x 
      exfalso 
      exact hz1 (by linarith) 
    · -- x^2 + x * z + z^2 + a * (x + z) + b = 0 
      linarith

  have eq4 : (x - z) * (x + y + z + a) = 0 := by
    nlinarith [eq1, eq2]

  have eq5 : x + y + z + a = 0 := by
    cases (mul_eq_zero.mp eq4) with
    | inl h11 =>
      exfalso 
      apply hz1
      linarith 
    | inr h12 =>
      linarith

  have ha : a = -(x + y + z) := by linarith
  have eq6 : b = x * y + x * z + y * z := by 
    rw [ha] at eq1
    nlinarith

  rw [show a = -(x + y + z) by linarith [ha]]
  rw [show b = x * y + x * z + y * z by linarith [eq6]]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
    sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h'
      apply hx1 
      linarith
    ), sq_pos_of_ne_zero (show y - z ≠ 0 by 
      intro h'
      apply hy1 
      linarith 
    ), sq_pos_of_ne_zero (show z - x ≠ 0 by 
      intro h'
      apply hz1 
      linarith 
    )
  ]