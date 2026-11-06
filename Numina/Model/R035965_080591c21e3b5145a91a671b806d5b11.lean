import Mathlib

theorem algebra_106351 {x y : ℝ} (hx : x + y = 30) (hy : x * y = 200) :
    x = 10 ∧ y = 20 ∨ x = 20 ∧ y = 10 := by
  have h1 : y = 30 - x := by linarith
  rw [h1] at hy
  have h2 : x^2 - 30 * x + 200 = 0 := by 
    nlinarith
  have h3 : (x - 10) * (x - 20) = 0 := by
    nlinarith [h2]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case $x = 10$, then $y = 20$.
    have hx10 : x = 10 := by linarith
    have hy20 : y = 20 := by 
      rw [hx10] at h1 
      linarith
    left 
    exact ⟨hx10, hy20⟩
  · -- Case $x = 20$, then $y = 10$.
    have hx20 : x = 20 := by linarith
    have hy10 : y = 10 := by 
      rw [hx20] at h1 
      linarith
    right 
    exact ⟨hx20, hy10⟩