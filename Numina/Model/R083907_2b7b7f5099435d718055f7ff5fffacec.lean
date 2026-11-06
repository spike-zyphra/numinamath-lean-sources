import Mathlib

theorem algebra_145229 (c : ℝ) (f : ℝ → ℝ) (hf : f = fun x => 2 * x ^ 2 + 3 * x + c)
    (hvertex : ∃ x y, x < 0 ∧ y < 0 ∧ f x = y ∧ deriv f x = 0) :
    c < 9 / 8 := by 
  rcases hvertex with ⟨x, y, hx1, hy1, hf_eq, hderiv_eq⟩
  have h_deriv : deriv f x = 4 * x + 3 := by
    rw [hf]
    simp [deriv_pow, deriv_add, deriv_mul, deriv_id', mul_comm]
    <;> field_simp
    <;> ring
  rw [h_deriv] at hderiv_eq
  have hx2 : x = -3 / 4 := by
    linarith
  rw [hf] at hf_eq
  simp at hf_eq
  rw [hx2] at hf_eq
  linarith