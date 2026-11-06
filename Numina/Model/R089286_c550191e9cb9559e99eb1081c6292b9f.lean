import Mathlib

open Real

theorem calculus_155362 (f : ℝ → ℝ) (hf : f = fun x => 1 / x) :
    deriv f = fun x => -1 / x ^ 2 := by
  rw [hf]
  funext x
  simp [deriv_div, deriv_const, deriv_id', pow_two, div_pow, sub_eq_add_neg, mul_comm]
  <;> ring_nf <;> simp [pow_two, div_pow]
  <;> ring