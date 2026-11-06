import Mathlib

theorem algebra_305757 {a b c d : ℝ} (h : a ≠ 0) (h1 : b ≠ 0) (h2 : c ≠ 0)
    (h3 : d ≠ 0) (h4 : a / b = b / c) (h5 : b / c = c / d) (h6 : c / d = d / a) :
    (a * b + b * c + c * d + d * a) / (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = 1 ∨
    (a * b + b * c + c * d + d * a) / (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = -1 := by

  have eq1 : a * c = b ^ 2 := by 
    field_simp [h1, h2] at h4
    nlinarith

  have eq2 : b * d = c ^ 2 := by 
    field_simp [h2, h3] at h5 
    nlinarith

  have eq3 : c * a = d ^ 2 := by 
    field_simp [h3, h] at h6 
    nlinarith

  have eq4 : d ^ 2 = b ^ 2 := by
    nlinarith [eq1, eq3]

  have h7 : d = b ∨ d = -b := by 
    have h8 : d ^ 2 - b ^ 2 = 0 := by 
      nlinarith 
    have h9 : (d - b) * (d + b) = 0 := by
      ring_nf at h8 ⊢ 
      nlinarith 
    cases (mul_eq_zero.mp h9) with 
    | inl h10 => 
      left 
      linarith 
    | inr h11 => 
      right 
      nlinarith

  cases h7 with
  | inl h7 =>
    have eq6 : b * b = c ^ 2 := by 
      rw [show d = b by linarith [h7]] at eq2
      linarith 
    have eq7 : c = b ∨ c = -b := by 
      have h8 : c ^ 2 - b ^ 2 = 0 := by 
        nlinarith 
      have h9 : (c - b) * (c + b) = 0 := by 
        ring_nf at h8 ⊢ 
        nlinarith 
      cases (mul_eq_zero.mp h9) with 
      | inl h10 => 
        left 
        linarith 
      | inr h11 => 
        right 
        nlinarith 
    cases eq7 with 
    | inl eq7 =>
      have eq8 : a * b = b ^ 2 := by 
        rw [show c = b by linarith [eq7]] at eq1 
        linarith 
      have eq9 : a = b := by 
        apply (mul_left_inj' h1).mp 
        linarith 
      left 
      field_simp [h, h1, h2, h3]
      <;> 
      nlinarith [sq_pos_of_ne_zero h, sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2, sq_pos_of_ne_zero h3, sq_nonneg (b^2)]
    | inr eq7 =>
      have eq8 : a * (-b) = b ^ 2 := by 
        rw [show c = -b by linarith [eq7]] at eq1 
        linarith 
      have eq9 : a = -b := by 
        apply (mul_left_inj' h1).mp 
        linarith 
      right 
      field_simp [h, h1, h2, h3]
      <;> 
      nlinarith [sq_pos_of_ne_zero h, sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2, sq_pos_of_ne_zero h3, sq_nonneg (b^2)]
  | inr h7 =>
    rw [show d = -b by linarith [h7]] at eq2 
    have eq9 : - (b ^ 2) = c ^ 2 := by 
      nlinarith 
    have eq10 : b ^ 2 = 0 := by 
      nlinarith [sq_nonneg c, sq_nonneg (b ^ 2)]
    have eq11 : b = 0 := by 
      nlinarith 
    contradiction