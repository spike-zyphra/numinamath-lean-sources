import Mathlib

theorem algebra_304819 {p : ℝ} (hp : p > 0) (h : ∃ x y, x ≠ y ∧ x^2 + p * x + 1 = 0 ∧ y^2 + p * y + 1 = 0 ∧ |x - y| = 1) :
    p = Real.sqrt 5 := by 
  rcases h with ⟨x, y, hxy, hx, hy, h1⟩
  have h2 : (x - y) ^ 2 = 1 := by 
    cases eq_or_eq_neg_of_abs_eq h1 with
    | inl h_eq =>
      have : x - y = 1 := by linarith 
      nlinarith
    | inr h_eq =>
      have : x - y = -1 := by linarith 
      nlinarith
  have h3 : (x - y) * (x + y + p) = 0 := by
    have eq1 : x^2 + p * x + 1 = 0 := hx
    have eq2 : y^2 + p * y + 1 = 0 := hy 
    have eq3 : (x^2 + p * x + 1) - (y^2 + p * y + 1) = 0 := by 
      nlinarith
    nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
      intro h_eq
      apply hxy
      linarith
    )]
  have h4 : x + y + p = 0 := by 
    cases' (mul_eq_zero.mp h3) with h5 h6 
    · -- Case x - y = 0 
      exfalso 
      have h5' : x = y := by 
        linarith 
      -- Contradicts to hxy: x ≠ y
      exfalso 
      tauto 
    · -- Case x + y + p = 0 
      linarith
  have h5 : x + y = -p := by 
    nlinarith [h4]
  have h8 : (x * y) = 1 := by
    nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
      intro h_eq
      apply hxy
      linarith
    ), sq_nonneg (x + y), h5, hx, hy, h2]
  have h7 : (x + y) ^2 = 5 := by
    nlinarith [h5, h2, h8]
  have h9 : p ^2 = 5 := by 
    have h5' : x + y = -p := h5
    have eq1 : (x + y) ^2 = p ^2 := by
      rw [h5']
      ring
    nlinarith [h7, eq1]
  have h10 : p = Real.sqrt 5 := by 
    have hp2 : p ^2 = 5 := h9 
    have hp_pos : p > 0 := hp
    have h9' : p = Real.sqrt 5 := by 
      rw [← hp2]
      field_simp
    exact h9'
  exact h10