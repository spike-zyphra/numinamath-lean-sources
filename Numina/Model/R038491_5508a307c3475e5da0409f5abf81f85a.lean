import Mathlib

theorem algebra_321124 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : (3 * a ^ 2 - 4 * a - 1) * (3 * a ^ 2 - 4 * a - 5) = 12)
    (h' : (3 * b ^ 2 - 4 * b - 1) * (3 * b ^ 2 - 4 * b - 5) = 12)
    (h'' : a + b > 2) (h''' : a + 2 > b) (h'''' : b + 2 > a) :
    a + b + 2 = 16 / 3 ∨ a + b + 2 = 20 / 3 := by

  have h1 : (3 * a ^ 2 - 4 * a - 7) * (3 * a ^ 2 - 4 * a + 1) = 0 := by
    nlinarith 
  have h2 : (3 * a ^ 2 - 4 * a - 7) = 0 ∨ (3 * a ^ 2 - 4 * a + 1) = 0 := by
    cases (mul_eq_zero.mp h1) with
    | inl h3 => 
      left
      linarith
    | inr h4 => 
      right
      linarith

  have h3 : (3 * b ^ 2 - 4 * b - 7) * (3 * b ^ 2 - 4 * b + 1) = 0 := by
    nlinarith 
  have h4 : (3 * b ^ 2 - 4 * b - 7) = 0 ∨ (3 * b ^ 2 - 4 * b + 1) = 0 := by
    cases (mul_eq_zero.mp h3) with
    | inl h33 => 
      left
      linarith
    | inr h44 => 
      right
      linarith

  have ha1 : a = 7/3 ∨ a = -1 ∨ a = 1 ∨ a = 1/3 := by
    cases h2 with
    | inl h5 =>
      have h7 : 3 * a ^ 2 - 4 * a - 7 = 0 := by linarith
      have h8 : (a - 7/3) * (a + 1) = 0 := by 
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 => 
        left
        linarith
      | inr h10 => 
        have h11 : a = -1 := by linarith
        simp [h11]
    | inr h6 =>
      have h7 : 3 * a ^ 2 - 4 * a + 1 = 0 := by linarith
      have h8 : (a - 1) * (a - 1/3) = 0 := by 
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 => 
        have h10 : a = 1 := by linarith
        simp [h10]
      | inr h11 => 
        have h12 : a = 1/3 := by linarith
        simp [h12]

  have hb1 : b = 7/3 ∨ b = -1 ∨ b = 1 ∨ b = 1/3 := by
    cases h4 with
    | inl h5 =>
      have h7 : 3 * b ^ 2 - 4 * b - 7 = 0 := by linarith
      have h8 : (b - 7/3) * (b + 1) = 0 := by 
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 => 
        left
        linarith
      | inr h10 => 
        have h11 : b = -1 := by linarith
        simp [h11]
    | inr h6 =>
      have h7 : 3 * b ^ 2 - 4 * b + 1 = 0 := by linarith
      have h8 : (b - 1) * (b - 1/3) = 0 := by 
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 => 
        have h10 : b = 1 := by linarith
        simp [h10]
      | inr h11 => 
        have h12 : b = 1/3 := by linarith
        simp [h12]

  rcases ha1 with (ha1 | ha1 | ha1 | ha1) <;> rcases hb1 with (hb1 | hb1 | hb1 | hb1) <;> 
    try { 
      nlinarith 
    } <;> try { 
      norm_num [ha1, hb1] at h'' h''' h'''' ⊢ 
      all_goals 
        try { tauto } 
    }