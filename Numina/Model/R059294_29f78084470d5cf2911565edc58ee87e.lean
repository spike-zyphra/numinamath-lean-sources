import Mathlib

theorem algebra_2427 {x y : ℝ} (hx : x^2 + 667 * x + 1992 = 0) (hy : y^2 + 667 * y + 1992 = 0)
    (hxy : x > y) : -1 / x = 1 / 3 := by
  have hx1 : x ≠ 0 := by
    nlinarith
  have hy1 : y ≠ 0 := by
    nlinarith

  have hx2 : (x + 3) * (x + 664) = 0 := by
    nlinarith
  
  have hy2 : (y + 3) * (y + 664) = 0 := by
    nlinarith
  
  have h1 : x + 3 = 0 ∨ x + 664 = 0 := by
    cases (mul_eq_zero.mp hx2) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  
  have h2 : y + 3 = 0 ∨ y + 664 = 0 := by
    cases (mul_eq_zero.mp hy2) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  
  cases h1 with
  | inl h3 =>
    have hx_eq : x = -3 := by linarith 
    rw [hx_eq]
    norm_num
  | inr h4 =>
    have hx_eq : x = -664 := by linarith
    cases h2 with
    | inl h3 =>
      have hy_eq : y = -3 := by linarith
      linarith
    | inr h5 =>
      have hy_eq : y = -664 := by linarith
      linarith