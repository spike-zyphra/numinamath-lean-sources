import Mathlib
open Finset

/- Determine the value of the sum 
$$
\frac{3}{1^2\cdot2^2}+\frac{5}{2^2\cdot3^2}+\frac{7}{3^2\cdot4^2}+\cdots+\frac{29}{14^2\cdot15^2}
$$ -/
theorem algebra_610977 : ∑ i ∈ range 14, (2 * i + 3: ℝ) / ((i + 1)^2 * (i + 2)^2: ℝ) = 224 / 225 := by
  -- Define `an i` as $a_n = \frac{2i+3}{(i+1)^2(i+2)^2}$ for each term in our series, and `bn i` as $1/(n+1)^2$.
  let an (i: ℕ) := (2 * i + 3: ℝ) / ((i + 1)^2 * (i + 2)^2: ℝ)
  let bn (i: ℕ) := 1 / (i + 1: ℝ)^2
  -- We have $an i = bn i - bn (i + 1)$
  have han_2_bn (i: ℕ): an i = bn i - bn (i + 1) := by
    unfold an bn
    calc
      _ = 1 / (i + 1: ℝ) ^ 2 - 1 / (i + 1 + 1: ℝ) ^ 2  := by field_simp; ring_nf
      _ = bn i - bn (i + 1)  := by unfold bn; simp
  -- replace $an i$ with $bn i - bn (i + 1)$ to transform the sum into a telescoping series.
  have hrw : ∑ i ∈ range 14, an i = - ∑ i ∈ range 14, (bn (i + 1) - bn i) := by
    rw [← Finset.sum_neg_distrib]
    congr
    ext x
    rw [han_2_bn x]
    simp
  -- now we need to show that - (bn 14 - bn 0) = 224 / 225, which is very easy.
  rw [hrw, Finset.sum_range_sub bn 14]
  unfold bn
  norm_num