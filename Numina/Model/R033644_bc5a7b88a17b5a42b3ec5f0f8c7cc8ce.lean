import Mathlib

theorem algebra_296571 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : (3 * a ^ 2 - 4 * a - 1) * (3 * a ^ 2 - 4 * a - 5) = 12)
    (h' : (3 * b ^ 2 - 4 * b - 1) * (3 * b ^ 2 - 4 * b - 5) = 12)
    (h'' : a + b > 2) (h''' : a + 2 > b) (h'''' : b + 2 > a) :
    a + b + 2 = 16 / 3 ∨ a + b + 2 = 20 / 3 := by

  have eq1 : (3 * a ^ 2 - 4 * a - 1) * (3 * a ^ 2 - 4 * a - 5) = 12 := h
  have eq2 : (3 * b ^ 2 - 4 * b - 1) * (3 * b ^ 2 - 4 * b - 5) = 12 := h'

  have h1 : (3 * a ^ 2 - 4 * a - 1) * (3 * a ^ 2 - 4 * a - 5) - 12 = 0 := by linarith
  have h2 : (3 * b ^ 2 - 4 * b - 1) * (3 * b ^ 2 - 4 * b - 5) - 12 = 0 := by linarith

  have h3 : (3 * a ^ 2 - 4 * a) ^ 2 - 6 * (3 * a ^ 2 - 4 * a) - 7 = 0 := by
    nlinarith [h1]

  have h4 : (3 * b ^ 2 - 4 * b) ^ 2 - 6 * (3 * b ^ 2 - 4 * b) - 7 = 0 := by
    nlinarith [h2]

  have h5 : (3 * a ^ 2 - 4 * a - 7) * (3 * a ^ 2 - 4 * a + 1) = 0 := by
    nlinarith [h3]

  have h6 : (3 * b ^ 2 - 4 * b - 7) * (3 * b ^ 2 - 4 * b + 1) = 0 := by
    nlinarith [h4]

  have ha1 : a = 1 ∨ a = 1 / 3 ∨ a = 7 / 3 := by
    cases (mul_eq_zero.mp h5) with
    | inl h7 =>
      -- Solving 3a^2 - 4a - 7 = 0
      have h8 : 3 * a ^ 2 - 4 * a - 7 = 0 := by linarith
      have h9 : (a - 7 / 3) * (a + 1) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h9) with
      | inl h10 =>
        right
        right
        linarith
      | inr h11 =>
        linarith -- contradiction with a > 0
    | inr h6 =>
      -- Solving 3a^2 - 4a + 1 = 0
      have h7 : 3 * a ^ 2 - 4 * a + 1 = 0 := by linarith
      have h8 : (a - 1) * (a - 1 / 3) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 =>
        left
        linarith
      | inr h10 =>
        right
        left
        linarith

  have hb1 : b = 1 ∨ b = 1 / 3 ∨ b = 7 / 3 := by
    cases (mul_eq_zero.mp h6) with
    | inl h7 =>
      -- Solving 3b^2 - 4b - 7 = 0
      have h8 : 3 * b ^ 2 - 4 * b - 7 = 0 := by linarith
      have h9 : (b - 7 / 3) * (b + 1) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h9) with
      | inl h10 =>
        right
        right
        linarith
      | inr h11 =>
        linarith -- contradiction with b > 0
    | inr h6 =>
      -- Solving 3b^2 - 4b + 1 = 0
      have h7 : 3 * b ^ 2 - 4 * b + 1 = 0 := by linarith
      have h8 : (b - 1) * (b - 1 / 3) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 =>
        left
        linarith
      | inr h10 =>
        right
        left
        linarith

  rcases ha1 with ha1 | ha1 | ha1 <;> rcases hb1 with hb1 | hb1 | hb1 <;> 
    -- Case analysis to check the valid perimeters
    try { 
      exfalso
      nlinarith 
    }
    <;> 
    -- Case analysis to check the valid perimeters
    try { 
      left
      linarith 
    }
    <;> 
    -- Case analysis to check the valid perimeters
    try { 
      right
      linarith 
    }