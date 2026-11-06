import Mathlib

theorem algebra_241052 (c : ℝ) (h : ∃ x1 x2, x1 ≠ x2 ∧ 27*x1^2-12*x1+c=0 ∧ 27*x2^2-12*x2+c=0 ∧ x1=x2^2) :
    c=1 ∨ c=-64 := by
  rcases h with ⟨x1, x2, hx12, h1, h2, h3⟩
  have eq1 : 27 * x1 ^ 2 - 12 * x1 + c = 0 := by linarith
  have eq2 : 27 * x2 ^ 2 - 12 * x2 + c = 0 := by linarith
  have h4 : 27 * (x1 ^ 2 - x2 ^ 2) - 12 * (x1 - x2) = 0 := by 
    nlinarith
  have h5 : (x1 - x2) * (27 * (x1 + x2) - 12) = 0 := by
    linarith [h4]
  cases (mul_eq_zero.mp h5) with
  | inl h6 =>
    exfalso 
    apply hx12
    linarith
  | inr h7 =>
    have h6 : x1 + x2 = 4 / 9 := by 
      linarith
    rw [show x1 = x2 ^ 2 by linarith [h3]] at h6
    have h8 : x2 ^ 2 + x2 - 4 / 9 = 0 := by
      nlinarith
    have h9 : (x2 - 1/3) * (x2 + 4/3) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h9) with 
    | inl h10 =>
      have hx2 : x2 = 1 / 3 := by linarith [h10]
      have hx1 : x1 = 1 / 9 := by 
        nlinarith [h3, hx2]
      have hc : c = 1 := by
        nlinarith [h1, hx1]
      left 
      exact hc
    | inr h11 =>
      have hx2 : x2 = -4 / 3 := by linarith [h11]
      have hx1 : x1 = 16 / 9 := by 
        nlinarith [h3, hx2]
      have hc : c = -64 := by
        nlinarith [h1, hx1]
      right 
      exact hc