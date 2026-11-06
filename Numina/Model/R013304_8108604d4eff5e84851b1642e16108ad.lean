import Mathlib

theorem algebra_10457 (x1 x2 : ℝ) (hx1 : (3 * x1 + 5) * (2 * x1 - 9) = 0) (hx2 : (3 * x2 + 5) * (2 * x2 - 9) = 0)
    (hx12 : x1 ≠ x2) : x1 + x2 = 17 / 6 := by

  have h1 : 3 * x1 + 5 = 0 ∨ 2 * x1 - 9 = 0 := by
    cases (mul_eq_zero.1 hx1) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith

  have h2 : 3 * x2 + 5 = 0 ∨ 2 * x2 - 9 = 0 := by
    cases (mul_eq_zero.1 hx2) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith

  cases h1 with
  | inl h1l =>
    cases h2 with
    | inl h2l =>
      exfalso
      apply hx12
      linarith
    | inr h2r =>
      have hx1_eq : x1 = -5 / 3 := by linarith
      have hx2_eq : x2 = 9 / 2 := by linarith
      linarith [hx1_eq, hx2_eq]
  | inr h1r =>
    cases h2 with
    | inl h2l =>
      have hx1_eq : x1 = 9 / 2 := by linarith
      have hx2_eq : x2 = -5 / 3 := by linarith
      linarith [hx1_eq, hx2_eq]
    | inr h2r =>
      exfalso
      apply hx12
      linarith