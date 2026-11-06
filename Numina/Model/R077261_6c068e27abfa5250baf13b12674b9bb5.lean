import Mathlib

theorem algebra_289366 (x y z : ℝ) (h₀ : x^2 - y = z^2) (h₁ : y^2 - z = x^2)
    (h₂ : z^2 - x = y^2) :
    (x, y, z) = (0, 0, 0) ∨ (x, y, z) = (1, 0, -1) ∨ (x, y, z) = (0, -1, 1) ∨
    (x, y, z) = (-1, 1, 0) := by
  have h3 : x + y + z = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h4 : z = -x - y := by linarith
  rw [h4] at h₀
  have h5 : y * (y + 2 * x + 1) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h5) with
  | inl hy0 =>
    have hy0 : y = 0 := by linarith
    have h6 : z = -x := by linarith [h4, hy0]
    have h7 : x * (x - 1) = 0 := by 
      rw [hy0, h6] at h₁
      nlinarith
    cases (mul_eq_zero.mp h7) with
    | inl hx0 =>
      have hx0 : x = 0 := by linarith
      have hz0 : z = 0 := by linarith [h6, hx0]
      left 
      simp [hx0, hy0, hz0]
    | inr hx1 =>
      have hx1 : x = 1 := by linarith
      have hz1 : z = -1 := by linarith [h6, hx1]
      right 
      left 
      simp [hx1, hy0, hz1]
  | inr hy1 =>
    have h8 : y + 2 * x + 1 = 0 := by linarith
    have h9 : z = x + 1 := by 
      nlinarith
    rw [h9, show y = -2 * x - 1 by linarith [h8] ] at h₂ 
    have h10 : 3 * x * (x + 1) = 0 := by 
      nlinarith
    cases (mul_eq_zero.mp h10) with
    | inl hx0 =>
      have hx0 : x = 0 := by linarith 
      have hz0 : z = 1 := by linarith [h9, hx0]
      have hy0 : y = -1 := by linarith [show y = -2 * x - 1 by linarith [h8], hx0] 
      right 
      right 
      left 
      simp [hx0, hy0, hz0]
    | inr hx1 =>
      have hx1 : x = -1 := by linarith 
      have hz1 : z = 0 := by linarith [h9, hx1]
      have hy1 : y = 1 := by linarith [show y = -2 * x - 1 by linarith [h8], hx1]
      right 
      right 
      right 
      simp [hx1, hy1, hz1]
  all_goals nlinarith