import Mathlib

theorem calculus_155801 (s : ℝ → ℝ) (h₀ : s = fun t => 3 * t ^ 2 - 3 * t + 8) :
    deriv s 4 = 21 ∧ iteratedDeriv 2 s 4 = 6 := by 
  have h1 : deriv s 4 = 21 := by
    rw [h₀]
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals norm_num [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    <;> norm_num
    all_goals ring_nf <;> norm_num
  have hs1 : deriv s = fun t => 6 * t - 3 := by
    rw [h₀]
    funext t
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals norm_num [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals ring_nf <;> norm_num
  have h2 : iteratedDeriv 2 s 4 = 6 := by
    have eq1 : iteratedDeriv 2 s 4 = deriv (deriv s) 4 := by 
      simp [iteratedDeriv_succ, iteratedDeriv_one]
      <;> aesop
    rw [eq1]
    rw [hs1]
    simp [deriv_sub, deriv_mul, deriv_id', mul_comm]
    all_goals norm_num [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    all_goals ring_nf <;> norm_num
  constructor
  · exact h1
  · exact h2