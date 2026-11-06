import Mathlib

theorem algebra_322718 {x y : ℝ} (h1 : x^3 + x^3 * y^3 + y^3 = 17) (h2 : x + x * y + y = 5) :
    (x, y) = (1, 2) ∨ (x, y) = (2, 1) := by
  have h3 : x^3 + y^3 + (x * y) ^ 3 = 17 := by
    nlinarith
  have h4 : x + y + x * y = 5 := by
    nlinarith
  have eq1 : x * y = 5 - (x + y) := by
    nlinarith
  rw [show x^3 + y^3 + (x * y) ^ 3 = (x + y) ^ 3 - 3 * (x + y) * (x * y) + (x * y) ^ 3 by nlinarith] at h3
  rw [eq1] at h3
  have h8 : (x + y) = 3 ∨ (x + y) = 2 := by
    ring_nf at h3
    have h10 : (x + y - 3) * (x + y - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- First case is true, so x=3 - s=3
      left
      linarith
    · -- Second case is true, so s=2.
      right
      linarith
  cases h8 with
  | inl h10 =>
    have h11 : x * y = 2 := by
      nlinarith
    have h13 : y = 3 - x := by
      nlinarith
    rw [h13] at h11
    have h12 : (x - 1) * (x - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- First case is true, so x=1, then y=2.
      left
      have hx1 : x = 1 := by linarith
      have hy1 : y = 2 := by
        nlinarith
      simp [hx1, hy1]
    · -- Second case is true, so x=2, then y=1.
      right
      have hx2 : x = 2 := by linarith
      have hy2 : y = 1 := by
        nlinarith
      simp [hx2, hy2]
  | inr h10 =>
    have h11 : x * y = 3 := by
      nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 3)]