import Mathlib

theorem algebra_137669 (f : ℝ → ℝ) (hf : f = fun x => x^10 - (1/5)*x^5 + 7) :
    deriv f = fun x => 10*x^9 - x^4 := by
  rw [hf]
  funext x
  simp [deriv_sub, deriv_add, deriv_pow, deriv_const, mul_comm]
  <;> field_simp <;> ring_nf <;> field_simp <;> ring