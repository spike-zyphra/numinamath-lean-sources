import Mathlib

open Finset Real

/- Example 2: Prove that for any $n \in \mathbf{N}^{*}$, there is exactly one set of numbers $x_{1}, x_{2}, \cdots, x_{n}$ that satisfies the equation

$$

\left(1-x_{1}\right)^{2}+\left(x_{1}-x_{2}\right)^{2}+\cdots+\left(x_{n-1}-x_{n}\right)^{2}+x_{n}^{2}=\frac{1}{n+1} .

$$
 -/
theorem algebra_231766 {n : ℕ} :
    (∀ x : ℕ → ℝ, x 0 = 1 ∧ x (n + 1) = 0 → ∑ i ∈ range (n + 1), (x i - x (i + 1))^2 ≥ 1 / (n + 1))
    ∧ (∃ x : ℕ → ℝ, x 0 = 1 ∧ x (n + 1) = 0 ∧ ∑ i ∈ range (n + 1), (x i - x (i + 1))^2 = 1 / (n + 1)) := by
  -- we will need n + 1 positive several times
  have n_pos : n + 1 > (0 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
  constructor
  -- show the inequality; this is a consequence of Cauchy-Schwarz
  · intro x hx
    apply (div_le_iff₀' n_pos).mpr
    have ineq : (∑ i ∈ range (n + 1), 1 * (x i - x (i + 1)))^2
      ≤ (∑ i ∈ range (n + 1), 1 ^ 2) * (∑ i ∈ range (n + 1), (x i - x (i + 1))^2)
    · have := Real.sum_mul_le_sqrt_mul_sqrt (range (n + 1)) (fun i => 1) (fun i => x i - x (i + 1))
      rw [←sqrt_mul, Real.le_sqrt'] at this
      exact this
      conv_rhs => enter [2, i]; rw [one_mul]
      rw [Finset.sum_range_sub', hx.1, hx.2, sub_zero]
      exact zero_lt_one
      rw [one_pow, sum_const, card_range, nsmul_one]
      exact_mod_cast n_pos.le
    conv_lhs at ineq => enter [1, 2, i]; rw [one_mul]
    conv_lhs at ineq => arg 1; rw [Finset.sum_range_sub', hx.1, hx.2, sub_zero]
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one] at ineq
    exact ineq
  -- show the equality; this is a calculation
  use fun i => 1 - i / (n + 1)
  simp only [CharP.cast_eq_zero, zero_div, sub_zero, Nat.cast_add, Nat.cast_one,
    sub_sub_sub_cancel_left, true_and, and_imp]
  constructor
  rw [div_self n_pos.ne.symm, sub_self]
  conv_lhs => arg 2; intro i; rw [add_div, add_comm, add_sub_cancel_right]
  rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      pow_two, ←mul_assoc, mul_comm, mul_one_div, div_self n_pos.ne.symm, mul_one]