import Mathlib

theorem algebra_195732 {R : ℝ} (h : ∃ x y, x ≠ y ∧ x^2-2*x-R=0 ∧ y^2-2*y-R=0 ∧ |x-y| = 12) :
    R = 35 := by 
  rcases h with ⟨x, y, hxy, hx, hy, habs⟩
  cases eq_or_eq_neg_of_abs_eq habs with
  | inl hxy12 =>
    have h1 : (x - y) * (x + y - 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h1) with
    | inl hxy0 =>
      exfalso
      exact hxy (by linarith)
    | inr hxy2 =>
      have hx_eq : x = 7 := by
        have h1 : x + y = 2 := by linarith
        have h2 : x - y = 12 := by linarith [hxy12]
        have h3 : 2 * x = 14 := by
          nlinarith
        linarith
      have hr : R = 35 := by
        rw [hx_eq] at hx
        nlinarith
      exact hr
  | inr hxy12 =>
    have h1 : (x - y) * (x + y - 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h1) with
    | inl hxy0 =>
      exfalso
      exact hxy (by linarith)
    | inr hxy2 =>
      have hx_eq : x = -5 := by
        have h1 : x + y = 2 := by linarith
        have h2 : x - y = -12 := by linarith [hxy12]
        have h3 : 2 * x = -10 := by
          nlinarith
        linarith
      have hr : R = 35 := by
        rw [hx_eq] at hx
        nlinarith
      exact hr