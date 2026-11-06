import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155603 {f : ℝ → ℝ} (hf : f = λ x => cos (x/2 - x^5)) :
    deriv f = λ x => -(1/2 - 5*x^4)*sin (x/2 - x^5) := by
  rw [hf]
  funext x
  have h1 : deriv (fun (y : ℝ) => cos (y / 2 - y ^ 5)) x =
      -(1 / 2 - 5 * x ^ 4) * sin (x / 2 - x ^ 5) := by
    simp [deriv_sub, deriv_pow, deriv_div_const, deriv_id'', mul_comm]
    all_goals
      field_simp
      <;> ring_nf
      <;> field_simp
  simpa using h1