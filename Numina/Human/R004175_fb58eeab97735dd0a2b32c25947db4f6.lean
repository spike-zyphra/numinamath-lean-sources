import Mathlib

open Real

/- Prove that for any positive $x_{1}, x_{2}, \ldots, x_{n}$ and $y_{1}, y_{2}, \ldots, y_{n}$ the inequality

$$
\sum_{i=1}^{n} \frac{1}{x_{i} y_{i}} \geq \frac{4 n^{2}}{\sum_{i=1}^{n}\left(x_{i}+y_{i}\right)^{2}}
$$

holds. -/
theorem inequalities_240795 {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ∑ i, 1 / (x i * y i) ≥ 4 * n ^ 2 / ∑ i, (x i + y i) ^ 2 := by

  -- a property, sum of $x_i y_i$ is positive
  have l_pos_sumxy : 0 < ∑ i, x i * y i := by
    apply Finset.sum_pos
    . simp_all
    . refine Finset.univ_nonempty_iff.mpr ?_
      exact Fin.pos_iff_nonempty.mp hn

  -- Since $\left(x_{i}+y_{i}\right)^{2} \geq 4 x_{i} y_{i}$, we can get this
  have r1 : 4 * n ^ 2 / ∑ i, (x i + y i) ^ 2 ≤ n ^ 2 / ∑ i, (x i * y i) := by
    have t1 : 4 * ∑ i, (x i * y i) ≤ ∑ i, (x i + y i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      linarith [two_mul_le_add_sq (x i) (y i)]
    trans (4 * n ^ 2) / (4 * ∑ i, (x i * y i))
    . gcongr
    . apply le_of_eq
      rw [mul_div_mul_left]
      norm_num

  -- it is sufficient to prove that $$ \left(\sum_{i=1}^{n} \frac{1}{x_{i} y_{i}}\right)\left(\sum_{i=1}^{n} x_{i} y_{i}\right) \geq n^{2} $$
  apply r1.trans
  apply (div_le_iff₀ l_pos_sumxy).mpr

  -- it follows directly from the Cauchy-Schwarz inequality.
  rw [show (n : ℝ) ^ 2 = (∑ i ∈ (Finset.univ : Finset (Fin n)), 1) ^ 2 by simp]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  . intro i hi
    apply one_div_nonneg.mpr
    nlinarith [hx i, hy i]
  . intro i hi
    nlinarith [hx i, hy i]
  . intro i hi
    rw [one_pow, div_mul_cancel₀]
    nlinarith [hx i, hy i]
