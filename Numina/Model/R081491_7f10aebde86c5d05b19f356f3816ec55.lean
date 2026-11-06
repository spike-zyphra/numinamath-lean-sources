import Mathlib

theorem calculus_155338 (f : ℝ → ℝ) (hf : f = fun x => 2 * x ^ 3 * (x ^ 6 - 1)) :
    deriv f = fun x => 6 * x ^ 2 * (3 * x ^ 6 - 1) := by
  rw [hf]
  funext x
  simp [deriv_const, deriv_pow, deriv_sub, deriv_add, deriv_id'', mul_add, mul_assoc, add_mul, mul_assoc]
  <;> ring_nf
  <;> field_simp
  <;> ring
  <;> linarith
  all_goals tauto
  <;> try linarith
  <;> try aesop
  <;> try ring_nf