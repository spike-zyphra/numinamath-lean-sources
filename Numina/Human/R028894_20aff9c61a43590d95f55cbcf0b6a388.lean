import Mathlib

open Real Set
open scoped BigOperators

/- Example 4.2.6 Let $a_{1}, a_{2}, \cdots, a_{n}>0, a_{1}, a_{2}, \cdots, a_{n} \in[0,2]$, and satisfy $a_{1}+a_{2}+\cdots+a_{n}=n$, find the maximum value of the following expression.
$$S=a_{1}^{2}+a_{2}^{2}+\cdots+a_{n}^{2}$$ -/
theorem inequalities_600545 {n : ℕ} (a : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (h : ∀ i, a i ≤ 2) (hsum : ∑ i, a i = n) :
  ∑ i, (a i)^2 ≤ 2 * n + 1 := by
  -- First we prove that for each term, a_i^2 ≤ 2*a_i
  have h1 : ∀ i, (a i) ^ 2 ≤ 2 * (a i) := by
    intro i
    -- Establish that a_i is non-negative (actually positive by assumption)
    have h2 : 0 ≤ a i := by linarith [ha i]
    -- Recall that a_i ≤ 2
    have h3 : a i ≤ 2 := h i
    -- Use non-linear arithmetic to prove the inequality
    -- This uses the fact that (a_i - 2)² ≥ 0 and a_i² ≥ 0
    nlinarith [sq_nonneg (a i - 2), sq_nonneg (a i)]

  -- Apply the inequality to the sum: ∑a_i² ≤ ∑(2*a_i)
  have h2 : ∑ i, (a i) ^ 2 ≤ ∑ i, 2 * (a i) := by
    apply Finset.sum_le_sum
    intro i _
    exact h1 i

  -- Factor out the constant 2 from the sum: ∑(2*a_i) = 2*∑a_i
  have h3 : ∑ i, 2 * (a i) = 2 * (∑ i, (a i)) := by
    rw [Finset.mul_sum]

  -- Substitute the factored sum into our inequality
  rw [h3] at h2
  -- Use the fact that ∑a_i = n
  rw [hsum] at h2
  -- Complete the proof with linear arithmetic
  linarith
