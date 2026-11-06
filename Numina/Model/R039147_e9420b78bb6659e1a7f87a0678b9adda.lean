import Mathlib

theorem algebra_237581 {x y : ℝ} (h₀ : x^2 + y^2 = 15 * (x + y)) (h₁ : x^2 - y^2 = 3 * (x - y)) :
    (x, y) = (6, -3) ∨ (x, y) = (-3, 6) ∨ (x, y) = (0, 0) ∨ (x, y) = (15, 15) := by
  have h2 : (x - y) * (x + y - 3) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case $x - y = 0$, which means $x = y$
    have h4 : x = y := by linarith
    rw [show y = x by linarith [h4]] at h₀
    have h5 : 2 * x^2 - 30 * x = 0 := by
      nlinarith
    have h6 : 2 * x * (x - 15) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case $2 * x = 0$
      have hx0 : x = 0 := by linarith
      have hy0 : y = 0 := by linarith [h4, hx0]
      simp [hx0, hy0]
      <;> tauto
    · -- Case $x - 15 = 0$
      have hx15 : x = 15 := by linarith
      have hy15 : y = 15 := by linarith [h4, hx15]
      simp [hx15, hy15]
      <;> tauto
  · -- Case $x + y - 3 = 0$, which means $x + y = 3$
    have h7 : x + y = 3 := by linarith
    have h8 : y = 3 - x := by linarith
    rw [show y = 3 - x by linarith [h8]] at h₀
    have h9 : (x - 6) * (x + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- Case $x - 6 = 0$
      have hx6 : x = 6 := by linarith
      have hy1 : y = -3 := by linarith [h8, hx6]
      simp [hx6, hy1]
      <;> tauto
    · -- Case $x + 3 = 0$
      have hx3 : x = -3 := by linarith
      have hy6 : y = 6 := by linarith [h8, hx3]
      simp [hx3, hy6]
      <;> tauto