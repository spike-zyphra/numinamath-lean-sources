import Mathlib

theorem algebra_320139 (m : ℝ) (h : ∃ x, x^2 - 5 * x + m = 0 ∧ ∃ y, y^2 + m * y + 5 = 0 ∧ -x = y) :
    m = 5 ∨ m = -6 := by
  rcases h with ⟨x, hx₁, ⟨y, hy₁, hy₂⟩⟩
  have hy_eq : y = -x := by linarith 
  rw [hy_eq] at hy₁ 
  have eq_subtract : (m - 5) * (x + 1) = 0 := by 
    nlinarith [hx₁, hy₁]
  cases' (mul_eq_zero.mp eq_subtract) with h1 h2 
  · -- Case where $m - 5 = 0$, so $m = 5$ 
    left 
    linarith 
  · -- Case where $x + 1 = 0$, so $x = -1$ 
    have hx_eq : x = -1 := by linarith 
    rw [hx_eq] at hx₁ 
    have hm : m = -6 := by 
      nlinarith 
    right 
    linarith