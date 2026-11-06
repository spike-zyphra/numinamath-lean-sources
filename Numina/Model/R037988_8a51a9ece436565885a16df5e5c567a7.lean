import Mathlib

def f (x : ℝ) := x^2 - 3 * x + 2

theorem calculus_161940 :
    deriv f (-1) = -5 ∧ deriv f 0 = -3 ∧ deriv f 1 = -1 ∧ deriv f 2 = 1 := by
  have hf : f = fun x => x^2 - 3 * x + 2 := by
    funext x
    simp [f]
  have h1 : deriv f (-1) = -5 := by
    rw [hf]
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals norm_num
  have h2 : deriv f 0 = -3 := by
    rw [hf]
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals norm_num
  have h3 : deriv f 1 = -1 := by
    rw [hf]
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals norm_num
  have h4 : deriv f 2 = 1 := by
    rw [hf]
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals norm_num
  exact ⟨h1, h2, h3, h4⟩