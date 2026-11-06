import Mathlib

open Complex Polynomial Real

/- A polynomial of degree four with leading coefficient 1 and integer coefficients has two zeros, both of which are integers. Which of the following can also be a zero of the polynomial?
(A) (1+i*sqrt(11))/2 (B) (1+i)/2 (C) 1/2+i(D) 1+i/2(E) (1+i*sqrt(13))/2 -/
theorem algebra_95191 : ∃ (P : Polynomial ℂ), P.degree = 4 ∧ Monic P ∧ (∃ x y : ℤ, x ≠ y ∧ P.eval (x : ℂ) = 0 ∧ P.eval (y : ℂ) = 0) ∧ P.eval ((1 + Complex.I * Real.sqrt 11) / 2) = 0 := by
  -- Let P be the polynomial defined in the solution
  let P : Polynomial ℂ := X * (X - C 1) * (C 1 * X^2 + C (-1) * X + C 3)
  -- z is the root we want
  let z : ℂ := (1 + Complex.I * Real.sqrt 11) / 2
  
  use P
  -- P has degree 4
  have deg_four : P.degree = 4 := by
    rw [degree_mul, degree_mul, degree_X_sub_C, degree_X]
    simp [degree_add_eq_left_of_degree_lt, degree_sub_eq_left_of_degree_lt, degree_X_pow, degree_C] 
    norm_num
  -- P is monic
  have monic_P : Monic P := by 
    rw [Monic.def]
    repeat rw [leadingCoeff_mul]
    simp only [leadingCoeff_X, leadingCoeff_X_sub_C, leadingCoeff_quadratic]
    rw [leadingCoeff_quadratic]
    simp; simp
    
  -- P has two distinct integer roots
  have two_int_roots : (∃ x y : ℤ, x ≠ y ∧ P.eval (x : ℂ) = 0 ∧ P.eval (y : ℂ) = 0) := by
    use 0
    use 1
    constructor
    · simp
    constructor
    · repeat rw [eval_mul]
      rw [eval_X]
      simp
    repeat rw [eval_mul]
    rw [eval_sub, eval_X, eval_C]
    simp
  -- z is a root of P
  have is_root_P_z : P.eval z = 0 := by 
    repeat rw [eval_mul]
    rw [eval_sub, eval_add, eval_add, eval_mul, eval_mul, eval_C, eval_pow, eval_X, eval_C, eval_C]
    ring
    norm_num
    norm_cast
    have : 4 = 2 * 2 := by norm_num
    rw [this, pow_mul]
    norm_num
  
  exact ⟨deg_four, monic_P, two_int_roots, is_root_P_z⟩