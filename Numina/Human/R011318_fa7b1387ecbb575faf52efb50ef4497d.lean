import Mathlib

open Polynomial

/- Example 3.4 Try to find a sequence $\{f(n)\}_{n \geqslant 0}$, whose first 5 terms are $1,3,7$, 13,21, and whose general term $f(n)$ is a polynomial in $n$ of the lowest degree. -/
theorem algebra_239818 {f : ℝ[X]} (hf : f.eval 0 = 1 ∧ f.eval 1 = 3 ∧ f.eval 2 = 7 ∧ f.eval 3 = 13 ∧ f.eval 4 = 21)
    (hlow : ∀ g : ℝ[X], g.eval 0 = 1 ∧ g.eval 1 = 3 ∧ g.eval 2 = 7 ∧ g.eval 3 = 13 ∧ g.eval 4 = 21 → f.natDegree ≤ g.natDegree) :
    f = X ^ 2 + X + 1 := by
  -- We first show that X^2 + X + 1 satisfies the given conditions.
  specialize hlow (X ^ 2 + X + 1)
  norm_num at hlow
  -- We show X^2 + X + 1 is of degree 2.
  rw [show (X ^ 2 + X + 1 : ℝ[X]).natDegree = 2 by compute_degree!] at hlow
  apply Nat.lt_add_one_of_le at hlow
  -- We write f as aX^2 + bX + c, using lemma `as_sum_range'`.
  let a := f.coeff 2
  let b := f.coeff 1
  let c := f.coeff 0
  have hfeq : f = C a * X ^ 2 + C b * X + C c := by
    rw [as_sum_range' f 3 hlow]
    simp only [Finset.sum, Finset.range_val, Multiset.range_succ, Multiset.range_zero,
      Multiset.cons_zero, ← C_mul_X_pow_eq_monomial, Multiset.map_cons, pow_one,
      Multiset.map_singleton, pow_zero, mul_one, Multiset.sum_cons, Multiset.sum_singleton, a, b, c]
    ring
  -- Simplify `hf` using the expression of `f` above.
  simp only [hfeq, eval_add, eval_mul, eval_C, eval_pow, eval_X, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, zero_add, one_pow, mul_one] at hf
  -- Solve the system of linear equations using `linarith`.
  obtain ⟨ha, hb, hc⟩ : a = 1 ∧ b = 1 ∧ c = 1 := by
    refine ⟨?_, ?_, ?_⟩
    all_goals linarith
  -- Conclude that `f = X^2 + X + 1`.
  simp [hfeq, ha, hb, hc]
