import Mathlib

theorem algebra_182639 :
    ∃ P : Fin 7 → MvPolynomial (Fin 7) ℕ,
      ∀ x : Fin 7 → ℕ,
        (∑ i : Fin 7, x i) ^ 2 +
          2 * ∑ i : Fin 7, (x i) ^ 2 =
        ∑ i : Fin 7, (MvPolynomial.eval x (P i)) ^ 2 := by
  use λ i =>
    if i = 0 then
      MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 3
    else if i = 1 then
      MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 4
    else if i = 2 then
      MvPolynomial.X 2 + MvPolynomial.X 3 + MvPolynomial.X 5
    else if i = 3 then
      MvPolynomial.X 3 + MvPolynomial.X 4 + MvPolynomial.X 6
    else if i = 4 then
      MvPolynomial.X 0 + MvPolynomial.X 4 + MvPolynomial.X 5
    else if i = 5 then
      MvPolynomial.X 1 + MvPolynomial.X 5 + MvPolynomial.X 6
    else if i = 6 then
      MvPolynomial.X 2 + MvPolynomial.X 6 + MvPolynomial.X 0
    else
      0
  intro x
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]
  all_goals
    ring