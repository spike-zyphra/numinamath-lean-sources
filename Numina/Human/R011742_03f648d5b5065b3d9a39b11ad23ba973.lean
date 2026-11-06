import Mathlib

open Real Finset

namespace inequalities_57680

lemma abs_sub_mid_le {n : ℕ} (i : range n) :
    |(i + 1 : ℝ) - (↑n + 1) / 2| ≤ (n - 1) / 2 := by
  rw [abs_le]
  simp only [neg_le_sub_iff_le_add, tsub_le_iff_right]
  obtain ⟨i, hi⟩ := i
  simp only [mem_range] at hi
  field_simp
  constructor
  · rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    simp only [Nat.ofNat_pos, mul_le_mul_right]
    linarith [hi] 
  · norm_cast

end inequalities_57680

open inequalities_57680

/- $a_1,…,a_n$ are real numbers such that $a_1+…+a_n=0$ and $|a_1|+…+|a_n|=1$. Prove that :
$$|a_1+2a_2+…+na_n| \leq \frac{n-1}{2}$$ -/
theorem inequalities_57680 (n : ℕ) (a : ℕ → ℝ)
    (h₀ : ∑ i : range n, a i = 0) (h₁ : ∑ i : range n, |a i| = 1) :
    |∑ i : range n, (i + 1) * a i| ≤ (n - 1) / 2 := by
  calc
  -- Let $S = \sum_{i=0}^{n-1} (i+1) a_i$.
  -- 1. We start with $|S|$. We can write $S$ as $S - 0$. The term we subtract is chosen strategically:
  --    $$|S| = \left| \sum_{i=0}^{n-1} (i+1) a_i - \sum_{i=0}^{n-1} \frac{n+1}{2} a_i \right|$$
  --    This equality holds because $\sum_{i=0}^{n-1} \frac{n+1}{2} a_i = \frac{n+1}{2} \sum_{i=0}^{n-1} a_i = \frac{n+1}{2} \cdot 0 = 0$, 
  --    using condition (1).
    _ = |∑ i : range n, (i + 1) * a i - (∑ i : range n, (n + 1) / 2 * a i)| := by
      congr
      rw [← mul_sum]
      simp only [h₀, mul_zero, sub_zero]    
  -- 2. Combine the sums:
  --  $$|S| = \left| \sum_{i=0}^{n-1} \left( (i+1) - \frac{n+1}{2} \right) a_i \right|$$
    _ = |∑ i : range n, ((i + 1) - (n + 1) / 2) * a i| := by
      rw [← sum_sub_distrib]
      congr
      ext x
      ring
  --   3. Apply the triangle inequality ($|\sum x_j| \le \sum |x_j|$):
  --  $$|S| \leq \sum_{i=0}^{n-1} \left| \left( (i+1) - \frac{n+1}{2} \right) a_i \right|$$
    _ ≤ ∑ i : range n, |((i + 1) - (n + 1) / 2) * a i| := by
      apply Finset.abs_sum_le_sum_abs
  --   4. Use the property $|xy| = |x||y|$:\
  --  $$|S| \leq \sum_{i=0}^{n-1} \left| (i+1) - \frac{n+1}{2} \right| |a_i|$$\
  --  Now, we use a key lemma. \
  --  For an index $i \in \{0, 1, \ldots, n-1\}$),\
  --  $$\left| (i+1) - \frac{n+1}{2} \right| \leq \frac{n-1}{2}$$\
  --  We can prove this lemma by $i &lt; n$. \
  --  Then\
  --  $$|S| \leq \sum_{i=0}^{n-1} \frac{n-1}{2} |a_i|$$
    _ = ∑ i : range n, |(i + 1 : ℝ) - (n + 1) / 2| * |a i| := by
      congr
      ext ; rw [abs_mul]
  -- 5. Factor out the constant term $\frac{n-1}{2}$:
  --  $$|S| \leq \frac{n-1}{2} \sum_{i=0}^{n-1} |a_i|$$
    _ ≤ ∑ i : range n, (n - 1) / 2 * |a i| := by
      refine sum_le_sum fun i _ => ?_
      gcongr
      exact abs_sub_mid_le i
  -- 6. Using condition (2), $\sum_{i=0}^{n-1} |a_i| = 1$:
  --  $$|S| \leq \frac{n-1}{2} \cdot 1 = \frac{n-1}{2}$$
    _ = (n - 1) / 2 * ∑ i : range n, |a i| := by
      simp [mul_sum]
  -- Therefore,
  -- $$\left| \sum_{i=0}^{n-1} (i+1) a_i \right| \leq \frac{n-1}{2}$$
  -- This completes the proof.-/
    _ = (n - 1) / 2 := by
      rw [h₁, mul_one]

