import Mathlib

theorem algebra_487 (x : ℂ) (hx : 2*x^2-6*x+24=6) :
    x=3/2+3*Real.sqrt 3*Complex.I/2 ∨ x=3/2-3*Real.sqrt 3*Complex.I/2 := by
  have h1 : 2 * x ^ 2 - 6 * x + 18 = 0 := by
    have eq1 : 2 * x ^ 2 - 6 * x + 24 = 6 := hx
    calc
      2 * x ^ 2 - 6 * x + 18 = (2 * x ^ 2 - 6 * x + 24) - 6 := by ring
      _ = 6 - 6 := by rw [hx]
      _ = 0 := by ring
  have eq2 : x ^ 2 - 3 * x + 9 = 0 := by
    have eq1' : 2 * x ^ 2 - 6 * x + 18 = 0 := h1
    calc
      x ^ 2 - 3 * x + 9 = (2 * x ^ 2 - 6 * x + 18) / 2 := by ring_nf
      _ = 0 / 2 := by rw [eq1']
      _ = 0 := by ring
  have eq3 : x ^ 2 - 3 * x + 9 = 0 := eq2
  have eq4 : x - (3/2 + 3*Real.sqrt 3*Complex.I/2) = 0 ∨ x - (3/2 - 3*Real.sqrt 3*Complex.I/2) = 0 := by
    have eq5 : x^2 - 3*x +9 =0 := eq3
    have h2 : x^2 -3*x +9 = (x - (3/2 + 3*Real.sqrt 3*Complex.I/2)) * (x - (3/2 - 3*Real.sqrt 3*Complex.I/2)) := by
      simp [pow_two, Complex.ext_iff, mul_add, mul_comm, mul_assoc, Complex.I_mul_I, Real.sqrt_sq]
      ring_nf 
      <;> norm_num [Real.sqrt_sq]
      <;> ring
      <;> norm_num [Real.sqrt_sq]
    rw [h2] at eq5
    cases (mul_eq_zero.mp eq5) with
    | inl h3 => 
      left
      exact h3
    | inr h4 => 
      right
      exact h4
  cases eq4 with
  | inl h5 => 
    left
    exact eq_of_sub_eq_zero h5
  | inr h6 => 
    right
    exact eq_of_sub_eq_zero h6