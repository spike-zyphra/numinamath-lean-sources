import Mathlib

theorem calculus_155815 (s : ℝ → ℝ)
    (h₀ : ∀ t, s t = (1 / 4) * t ^ 4 + 4 * t ^ 3 + 16 * t ^ 2) :
    deriv (deriv s) 2 = 92 := by

  have eq1 : s = fun t => (1 / 4) * t^4 + 4 * t^3 + 16 * t^2 := by
    funext t
    simpa using h₀ t

  have eq2 : deriv s = fun t => t^3 + 12 * t^2 + 32 * t := by
    rw [eq1]
    funext t
    simp [deriv_pow, deriv_const, deriv_add, deriv_mul, mul_comm]
    <;> field_simp <;> ring_nf <;> norm_num

  have eq3 : deriv (deriv s) 2 = 92 := by
    rw [eq2]
    simp [deriv_pow, deriv_const, deriv_add, deriv_mul, mul_comm]
    <;> norm_num

  exact_mod_cast eq3