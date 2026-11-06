import Mathlib

open BigOperators Finset

/- Let $a_{1}, \ldots, a_{n}$ be real numbers such that: $\sum a_{i}=0$, and: $\sum\left|a_{i}\right|=1$. Show that: $\left|\sum i \cdot a_{i}\right| \leqslant \frac{n-1}{2}$. -/
theorem inequalities_157684
    (n : ℕ)
    (a : Fin n → ℝ)
    (h₀ : 0 < n)
    (h₁ : ∑ i, a i = 0)
    (h₂ : ∑ i, |a i| = 1)
    : |∑ i : Fin n, (i : ℝ) * a i| ≤ ((n : ℝ) - 1) / 2 := by
  -- Let c be the constant (n-1)/2.
  let c := ((n : ℝ) - 1) / 2
  -- We want to show that the sum can be rewritten by subtracting c from each index.
  have h_sum_eq : ∑ i : Fin n, (i : ℝ) * a i = ∑ i : Fin n, ((i : ℝ) - c) * a i := by
    -- Rewrite the sum by distributing (i - c) * a i.
    simp_rw [sub_mul]
    -- Simplify the resulting expression using the hypothesis that the sum of a_i is 0.
    simp [← mul_sum, h₁]
  -- Rewrite the goal using the equality we just proved.
  rw [h_sum_eq]
  -- Apply the triangle inequality.
  trans ∑ i : Fin n, |(↑↑i - c) * a i|
  -- The absolute value of a sum is less than or equal to the sum of the absolute values.
  · exact abs_sum_le_sum_abs (fun i => (↑↑i - c) * a i) univ
  -- Now, we work with the sum of absolute values.
  · simp_rw [abs_mul]
    -- We need to bound the term |i - c| for each i.
    have h_bound : ∀ (i : Fin n), |(i : ℝ) - c| ≤ c := by
      -- Introduce i.
      intro i
      -- Since n > 0, we know 1 <= n.
      have : 1 ≤ n := Nat.succ_le_of_lt h₀
      -- Show that c is non-negative.
      have hc_nonneg : 0 ≤ c := by
        -- Unfold c.
        simp [c]
        -- The numerator is non-negative because n >= 1, and the denominator is positive.
        apply div_nonneg (by simp [this]) (by norm_num)
      -- The inequality |x| <= c is equivalent to -c <= x <= c.
      rw [abs_le]
      -- Prove both sides of the inequality.
      constructor
      -- Prove the lower bound: -c <= i - c.
      · simp
      -- Prove the upper bound: i - c <= c.
      · simp [c]
        -- Rewrite (n:ℝ) - 1 as ((n-1):ℕ):ℝ.
        rw [show (n : ℝ) - 1 = (((n - 1) : ℕ) : ℝ) by simp [Nat.cast_sub this]]
        -- Cast the goal to natural numbers.
        norm_cast
        -- The goal is now i <= n - 1, which is true by definition of Fin n.
        exact Nat.le_sub_of_add_le (by omega)
    -- Use the bound we just proved to establish the inequality for the sum.
    calc
      -- The sum is less than or equal to the sum with |i - c| replaced by c.
      _ ≤ ∑ i, c * |a i| := by
        -- Apply the sum_le_sum tactic.
        apply sum_le_sum 
        -- For each i, we need to show |i - c| * |a i| <= c * |a i|.
        intro i _
        -- This follows from |i - c| <= c and the fact that |a i| is non-negative.
        exact mul_le_mul_of_nonneg_right (h_bound i) (abs_nonneg (a i))
      -- Factor out the constant c from the sum.
      _ = c * ∑ i, |a i| := by rw [Finset.mul_sum]
      -- Finally, use the hypothesis that the sum of |a i| is 1.
      _ = c := by simp [h₂]