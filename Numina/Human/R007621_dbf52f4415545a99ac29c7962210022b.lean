import Mathlib

open Polynomial

/- Let
$$
P(x) = x^{2022} + x^{1011} + 1.
$$
 Which of the following polynomials is a factor of $P(x)$?
$\textbf{(A)} \, x^2 -x + 1 \qquad\textbf{(B)} \, x^2 + x + 1 \qquad\textbf{(C)} \, x^4 + 1 \qquad\textbf{(D)} \, x^6 - x^3 + 1  \qquad\textbf{(E)} \, x^6 + x^3 + 1$ -/
theorem algebra_95199 :
    (X ^ 6 + X ^ 3 + 1) ∣ (X ^ 2022 + X ^ 1011 + 1 : ℤ[X]) := by
  -- We use the theory of cyclotomic polynomials to solve the problem.
  -- Firstly, we notice that x^6 + x^3 + 1 is precisely ψ_9
  -- This is because ψ_1 * ψ_3 * ψ_9 = x^9 - 1, and ψ_1 * ψ_3 = x^3 - 1.
  have h_cyclotomic_9 : (X ^ 6 + X ^ 3 + 1 : ℤ[X]) = cyclotomic 9 ℤ := by
    have h := @X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd ℤ _ 3 9
    have : (9).divisors \ (3).divisors = {9} := by
      rw [show Nat.divisors 9 = {1, 3, 9} by decide]
      rw [show Nat.divisors 3 = {1, 3} by decide]
      rfl
    simp only [Nat.mem_properDivisors, show 3 ∣ 9 by decide, true_and, this,
      Finset.prod_singleton, forall_const, show 3 < 9 by decide] at h
    rw [show (X ^ 9 - 1 : ℤ[X]) = (X ^ 3 - 1) * (X ^ 6 + X ^ 3 + 1) by ring_nf] at h
    apply (mul_left_cancel₀ _ h).symm
    exact X_pow_sub_C_ne_zero (by decide : 0 < 3) 1

  -- Next, we prove that x^2022 + x^1011 + 1 is ψ_9 * ψ_3033
  -- To see this, notice that divisors of 3033 are {1, 3, 9, 337, 1011, 3033}
  -- While the divisors of 1011 are {1, 3, 337, 1011}
  -- Hence, (x^3033 - 1) / (x^1011 - 1) = ψ_9 * ψ_3033
  -- And it can be verified that the LHS is x^2022 + x^2011 + 1.
  have h_cyclotomic_3033 :=
    @X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd ℤ _ 1011 3033 (by native_decide)
  have h_divs : Nat.divisors 3033 \ Nat.divisors 1011 = {9, 3033} := by
    rw [show Nat.divisors 3033 = {1, 3, 9, 337, 1011, 3033} by native_decide]
    rw [show Nat.divisors 1011 = {1, 3, 337, 1011} by native_decide]
    rfl
  rw [h_divs, show (X ^ 3033 - 1 : ℤ[X]) = (X ^ 1011 - 1) * (X ^ 2022 + X ^ 1011 + 1) by ring_nf]
    at h_cyclotomic_3033
  simp only [Finset.mem_singleton, Nat.reduceEqDiff, not_false_eq_true, Finset.prod_insert,
    Finset.prod_singleton, mul_eq_mul_left_iff] at h_cyclotomic_3033
  have := h_cyclotomic_3033.resolve_right (X_pow_sub_C_ne_zero (by decide : 0 < 1011) 1)

  -- Hence, the relation to be proven can be written as ψ_9 ∣ ψ_9 * ψ_3033, which is obvious.
  rw [← this, ← h_cyclotomic_9]
  exact dvd_mul_right (X ^ 6 + X ^ 3 + 1) (cyclotomic 3033 ℤ)