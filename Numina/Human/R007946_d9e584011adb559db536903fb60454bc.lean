import Mathlib

open Finset intervalIntegral

/- Prove that, for any real $a_{1}, a_{2}, \ldots, a_{n}$,

$$
\sum_{i, j=1}^{n} \frac{a_{i} a_{j}}{i+j-1} \geq 0
$$ -/
theorem inequalities_236970 (n : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, a i * a j / (i + j + 1) ≥ 0 := by
-- Denote $P$ to be the polynomial function $a_0+a_1 * x + a_2 * x^2 + ...$
  let P : ℝ → ℝ := fun x => ∑ i ∈ range n, a i * x ^ i
-- Prove that the integral of $P^2$ on $[0, 1]$ is nonnegative
  have Pint : 0 ≤ ∫ x in (0 : ℝ)..1, (P x) ^ 2 := by
    apply integral_nonneg; simp
    intros; positivity
-- Rewrite $P^2$ to a double summation and evaluate the integral in `Pint`, the goal follows
  dsimp [P] at Pint; simp [pow_two, sum_mul_sum] at Pint
  rw [integral_finset_sum] at Pint; rw [ge_iff_le]
  apply le_trans Pint; apply sum_le_sum
  · intro i hi; rw [integral_finset_sum]
    apply sum_le_sum
    · intro j hj; have : a i * a j / (i + j + 1) =
      ∫ x in (0 : ℝ)..1, a i * a j * x ^ (i + j) := by simp; ring
      rw [this]; apply le_of_eq; apply integral_congr
      intro x _; simp; ring
    intros; apply Continuous.intervalIntegrable; continuity
  intros; apply Continuous.intervalIntegrable; continuity