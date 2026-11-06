import Mathlib

theorem algebra_269403 {x y : ℝ} (h1 : x * y * (x ^ 2 + y ^ 2) = 78) (h2 : x ^ 4 + y ^ 4 = 97) :
    (x = 3 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ∨ (x = -3 ∧ y = -2) ∨ (x = -2 ∧ y = -3) := by
  have h3 : (x + y) ^ 2 = 25 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y)]
  have h4 : x + y = 5 ∨ x + y = -5 := by
    have h5 : (x + y) ^ 2 - 25 = 0 := by nlinarith
    have h6 : (x + y - 5) * (x + y + 5) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h6) with
    | inl h7 => 
      left
      linarith
    | inr h8 => 
      right
      linarith
  cases h4 with
  | inl h4 => 
    have h5 : x * y = 6 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 5), sq_nonneg (x * y)]
    have h6 : (x - 2) * (x - 3) = 0 := by
      nlinarith 
    cases (mul_eq_zero.1 h6) with
    | inl h7 => 
      have hx2 : x = 2 := by linarith
      have hy3 : y = 3 := by nlinarith
      simp [hx2, hy3]
      <;> tauto
    | inr h8 => 
      have hx3 : x = 3 := by linarith
      have hy2 : y = 2 := by nlinarith
      simp [hx3, hy2]
      <;> tauto
  | inr h4 => 
    have h5 : x * y = 6 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 5), sq_nonneg (x * y)]
    have h6 : (x + 2) * (x + 3) = 0 := by
      nlinarith 
    cases (mul_eq_zero.1 h6) with
    | inl h7 => 
      have hx2 : x = -2 := by linarith
      have hy3 : y = -3 := by nlinarith
      simp [hx2, hy3]
      <;> tauto
    | inr h8 => 
      have hx3 : x = -3 := by linarith
      have hy2 : y = -2 := by nlinarith
      simp [hx3, hy2]
      <;> tauto