import Mathlib


open Real


lemma lemma_1 {s : ℝ → ℝ} (hs : s = fun t => 2 * t^3 - 6 * t^2 + 4 * t) :
    deriv s = fun t => 6 * t^2 - 12 * t + 4 := by
  rw [hs]
  funext t
  simp [deriv_pow, deriv_const, deriv_id', mul_comm]
  <;> field_simp
    <;> ring
      <;> norm_num


theorem calculus_155808 (s : ℝ → ℝ) (h₀ : s = fun t => 2 * t ^ 3 - 6 * t ^ 2 + 4 * t) :
    deriv (deriv s) 3 = 24 := by
  have h1 : deriv s = fun t => 6 * t^2 - 12 * t + 4 := by
    exact lemma_1 h₀
  have h2 : deriv (deriv s) = fun t => 12 * t - 12 := by
    rw [h1]
    funext t
    simp [deriv_pow, deriv_const, deriv_id', mul_comm]
    <;> field_simp
      <;> ring
        <;> norm_num
  rw [h2]
  all_goals norm_num