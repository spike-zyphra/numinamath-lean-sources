import Mathlib

def f (x : ℝ) := 2 * x ^ 3 + 4 * x - 5

theorem calculus_140691 : deriv f 0 = 4 ∧ deriv f 1 = 10 ∧ deriv f 2 = 28 := by
  have hf : f = fun (x : ℝ) => 2 * x ^ 3 + 4 * x - 5 := by
    funext x
    simp [f]

  -- Compute the derivative at 0
  have h1 : deriv f 0 = 4 := by 
    rw [hf]
    simp [deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_id', mul_comm]
    all_goals norm_num

  -- Compute the derivative at 1
  have h2 : deriv f 1 = 10 := by
    rw [hf]
    simp [deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_id', mul_comm]
    all_goals norm_num

  -- Compute the derivative at 2
  have h3 : deriv f 2 = 28 := by
    rw [hf]
    simp [deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_id', mul_comm]
    all_goals norm_num

  -- Combine all results
  exact ⟨h1, h2, h3⟩