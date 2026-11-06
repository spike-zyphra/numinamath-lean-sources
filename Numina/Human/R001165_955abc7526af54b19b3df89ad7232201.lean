import Mathlib

/- The sum of the first $n$ terms in the infinite geometric sequence $\left\{\frac{1}{4},\frac{1}{8},\frac{1}{16},\dots \right\}$ is $\frac{255}{512}$. Find $n$. -/
theorem algebra_20812 (n : ℕ) (h : ∑ i ∈ Finset.range n, (1 / 4) * (1 / 2 : ℝ) ^ i = 255 / 512) :
    n = 8 := by
    -- use the formula for the partial sum of a geometric series
    rw [←Finset.mul_sum, geom_sum_eq (by linarith)] at h
    -- compare with the true answer n = 8
    have h1 : 1 / 4 * (((1 / 2) ^ 8 - 1) / (1 / 2 - 1)) = 255 / (512 : ℝ) := by norm_num
    -- use injectivity on all relevant operations to single out that n = 8.
    rw [← h1, mul_right_inj' (by norm_num), div_left_inj' (by norm_num),
    sub_left_inj, pow_right_inj (by norm_num) (by norm_num)] at h
    -- finally get n = 8
    exact h
