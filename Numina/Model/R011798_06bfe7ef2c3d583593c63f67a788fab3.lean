import Mathlib
open Polynomial

theorem algebra_604776 :
  ∃ (k n : ℕ),
    0 < k ∧ 0 < n ∧
    ∃ (x : Fin k → ℤ) (y : Fin n → ℤ),
      (∀ i j : Fin k, i ≠ j → x i ≠ x j) ∧
      (∀ i j : Fin n, i ≠ j → y i ≠ y j) ∧
      ∃ (P : Polynomial ℤ),
        (∀ i, P.eval (x i) = 54) ∧
        (∀ i, P.eval (y i) = 2013) ∧
        k * n = 6 := by
  use 2
  use 3
  constructor
  · norm_num
  constructor
  · norm_num
  use ![1, -1]
  use ![0, 2, -2]
  constructor
  · -- show that $x_i$ are distinct
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at *
    all_goals omega
  constructor
  · -- show that $y_i$ are distinct
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at *
    all_goals omega
  use (653 * X ^ 4 + -2612 * X ^ 2 + 2013)
  constructor
  · -- Show that $P(x_i) = 54$ for all $i$
    intro i
    fin_cases i <;> simp
    all_goals norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    <;> omega
  constructor
  · -- Show that $P(y_i) = 2013$ for all $i$
    intro i
    fin_cases i <;> simp
    all_goals norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    <;> omega
  · -- Show that k * n = 6
    norm_num