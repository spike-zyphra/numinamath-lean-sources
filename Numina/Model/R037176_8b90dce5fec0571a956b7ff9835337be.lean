import Mathlib
open Polynomial

/-Given the function $f(x)=x^{3}+ax^{2}+3x-9$, find the value of $a$ such that $f(x)$ attains an extreme value at $x=-3$.-/
noncomputable def f_9226 (a : ℝ) : Polynomial ℝ := X^3 + (C a) * X^2 + 3 * X - 9

theorem algebra_9226 (a : ℝ) (h : IsLocalMax (f_9226 a).eval (-3)) :
    a = 5 := by
  have h1 : deriv (fun x : ℝ => (f_9226 a).eval x) (-3) = 0 := by
    apply h.deriv_eq_zero
  have eqn1 : deriv (fun x : ℝ => (f_9226 a).eval x) (-3) = 3 * (-3) ^ 2 + 2 * a * (-3) + 3 := by
    simp [f_9226]
    simp [deriv_pow, deriv_const, deriv_add, deriv_sub, deriv_mul, mul_comm]
    field_simp
    ring_nf
  rw [eqn1] at h1
  linarith