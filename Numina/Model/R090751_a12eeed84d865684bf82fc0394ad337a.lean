import Mathlib

theorem algebra_19306 {x : ℝ} (hx : 18*x^2 + 25*x - 3 = 0 ∧ 4*x^2 + 8*x + 3 = 0) :
    x = -3/2 := by
  rcases hx with ⟨h₁, h₂⟩
  have h3 : (2 * x + 1) * (2 * x + 3) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case $2x + 1 = 0$, which implies $x = -1/2$
    have hx1 : x = -1/2 := by linarith 
    rw [hx1] at h₁
    norm_num at h₁
  · -- Case $2x + 3 = 0$, which implies $x = -3/2$
    have hx2 : x = -3/2 := by linarith 
    linarith