import Mathlib

theorem algebra_132376 (x y z : ℝ) (h1 : (x - 2)^2 + (y + 1)^2 = 5) (h2 : (x - 2)^2 + (z - 3)^2 = 13)
    (h3 : (y + 1)^2 + (z - 3)^2 = 10) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = -2 ∧ z = 0) ∨ (x = 0 ∧ y = 0 ∧ z = 6) ∨
    (x = 0 ∧ y = -2 ∧ z = 6) ∨ (x = 4 ∧ y = 0 ∧ z = 0) ∨ (x = 4 ∧ y = -2 ∧ z = 0) ∨
    (x = 4 ∧ y = 0 ∧ z = 6) ∨ (x = 4 ∧ y = -2 ∧ z = 6) := by
  have h4 : (z - 3) ^ 2 = 9 := by
    nlinarith
  have h5 : z - 3 = 3 ∨ z - 3 = -3 := by 
    have h : (z - 3) ^ 2 - 9 = 0 := by linarith 
    have h6 : (z - 3 - 3) * (z - 3 + 3) = 0 := by
      nlinarith 
    cases (mul_eq_zero.1 h6) with
    | inl h8 =>
      left
      linarith
    | inr h7 =>
      right
      linarith
  cases h5 with
  | inl h5 =>
    have hz6 : z = 6 := by linarith 
    have h6 : (y + 1) ^ 2 = 1 := by 
      nlinarith 
    have h7 : y + 1 = 1 ∨ y + 1 = -1 := by
      have h8 : (y + 1) ^ 2 - 1 = 0 := by linarith 
      have h9 : (y + 1 - 1) * (y + 1 + 1) = 0 := by
        nlinarith 
      cases (mul_eq_zero.1 h9) with 
      | inl h10 =>
        left
        linarith
      | inr h11 =>
        right
        linarith
    cases h7 with
    | inl h7 =>
      have hy0 : y = 0 := by linarith 
      have h8 : (x - 2) ^ 2 = 4 := by 
        nlinarith 
      have h9 : x - 2 = 2 ∨ x - 2 = -2 := by
        have h10 : (x - 2) ^ 2 - 4 = 0 := by linarith 
        have h11 : (x - 2 - 2) * (x - 2 + 2) = 0 := by
          nlinarith 
        cases (mul_eq_zero.1 h11) with
        | inl h12 =>
          left
          linarith
        | inr h13 =>
          right
          linarith
      cases h9 with
      | inl h9 =>
        have hx4 : x = 4 := by linarith 
        simp [hx4, hy0, hz6]
        <;> tauto 
      | inr h9 =>
        have hx0 : x = 0 := by linarith 
        simp [hx0, hy0, hz6]
        <;> tauto 
    | inr h7 =>
      have hy2 : y = -2 := by linarith 
      have h8 : (x - 2) ^ 2 = 4 := by 
        nlinarith 
      have h9 : x - 2 = 2 ∨ x - 2 = -2 := by
        have h10 : (x - 2) ^ 2 - 4 = 0 := by linarith 
        have h11 : (x - 2 - 2) * (x - 2 + 2) = 0 := by
          nlinarith 
        cases (mul_eq_zero.1 h11) with
        | inl h12 =>
          left
          linarith
        | inr h13 =>
          right
          linarith
      cases h9 with
      | inl h9 =>
        have hx4 : x = 4 := by linarith 
        simp [hx4, hy2, hz6]
        <;> tauto 
      | inr h9 =>
        have hx0 : x = 0 := by linarith 
        simp [hx0, hy2, hz6]
        <;> tauto 
  | inr h5 =>
    have hz0 : z = 0 := by linarith 
    have h6 : (y + 1) ^ 2 = 1 := by 
      nlinarith 
    have h7 : y + 1 = 1 ∨ y + 1 = -1 := by
      have h8 : (y + 1) ^ 2 - 1 = 0 := by linarith 
      have h9 : (y + 1 - 1) * (y + 1 + 1) = 0 := by
        nlinarith 
      cases (mul_eq_zero.1 h9) with 
      | inl h10 =>
        left
        linarith
      | inr h11 =>
        right
        linarith
    cases h7 with
    | inl h7 =>
      have hy0 : y = 0 := by linarith 
      have h8 : (x - 2) ^ 2 = 4 := by 
        nlinarith 
      have h9 : x - 2 = 2 ∨ x - 2 = -2 := by
        have h10 : (x - 2) ^ 2 - 4 = 0 := by linarith 
        have h11 : (x - 2 - 2) * (x - 2 + 2) = 0 := by
          nlinarith 
        cases (mul_eq_zero.1 h11) with
        | inl h12 =>
          left
          linarith
        | inr h13 =>
          right
          linarith
      cases h9 with
      | inl h9 =>
        have hx4 : x = 4 := by linarith 
        simp [hx4, hy0, hz0]
        <;> tauto 
      | inr h9 =>
        have hx0 : x = 0 := by linarith 
        simp [hx0, hy0, hz0]
        <;> tauto 
    | inr h7 =>
      have hy2 : y = -2 := by linarith 
      have h8 : (x - 2) ^ 2 = 4 := by 
        nlinarith 
      have h9 : x - 2 = 2 ∨ x - 2 = -2 := by
        have h10 : (x - 2) ^ 2 - 4 = 0 := by linarith 
        have h11 : (x - 2 - 2) * (x - 2 + 2) = 0 := by
          nlinarith 
        cases (mul_eq_zero.1 h11) with
        | inl h12 =>
          left
          linarith
        | inr h13 =>
          right
          linarith
      cases h9 with
      | inl h9 =>
        have hx4 : x = 4 := by linarith 
        simp [hx4, hy2, hz0]
        <;> tauto 
      | inr h9 =>
        have hx0 : x = 0 := by linarith 
        simp [hx0, hy2, hz0]
        <;> tauto