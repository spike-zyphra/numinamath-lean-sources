import Mathlib
open Polynomial

/-Given the function $f(x)=x^{3}+ax^{2}+3x-9$, find the value of $a$ such that $f(x)$ attains an extreme value at $x=-3$.-/
noncomputable def f_9226 (a : ℝ) : Polynomial ℝ := X^3 + (C a) * X^2 + 3 * X - 9

theorem algebra_9226 (a : ℝ) (h : IsLocalMax (f_9226 a).eval (-3)) :
    a = 5 := by
    -- derivative on $f(x)=x^{3}+ax^{2}+3x-9$ when $x=-3 equal zero$
    have deriv_zero := h.deriv_eq_zero; simp at deriv_zero
    rw [f_9226] at deriv_zero; simp at deriv_zero
    -- after simplification, we get $a = 5$
    linarith
