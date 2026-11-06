import Mathlib

open Real

/- Express the infinite series $$\frac{3}{206}+\frac{9}{2\cdot103^2}+\frac{27}{2\cdot103^3}+\cdots$$as a terminating decimal. -/
theorem algebra_21345 : ∑' n : ℕ, ((3 * (3 ^ n)):ℝ) / (2 * (103 ^ (n + 1))) = 0.015 := by
  -- notice that it is a geometric sequence with common ratio 3/103
  let r : ℝ := 3/103
  have r_def: r = 3/103 := rfl
  -- extract 1/2, it is 1/2 (r+r^2+r^3+...)
  have h1:  ∑' n : ℕ, ((3 * (3 ^ n)):ℝ) / (2 * (103 ^ (n + 1))) =
    1/2 * (∑' n:ℕ, r^(n+1)) := by
    rw [← tsum_mul_left]
    congr
    ext k
    rw [r_def]
    field_simp; ring
  -- by geometric series sum formula, it is a1 / (1-r) = r/(1-r)
  have h2: (∑' n:ℕ, r^(n+1)) = r / (1-r) := by
    have hh1: (∑' n:ℕ, r^(n+1)) = r * (∑' n:ℕ, r^n) := by
      rw [← tsum_mul_left]
      congr
      ext k
      ring
    rw [hh1]
    have hh2: |r| < 1 := by
      have tt1: 0 ≤ r := by
        rw [r_def]; norm_num
      have tt2: |r| = r := by
        exact abs_of_nonneg tt1
      rw [tt2, r_def]; norm_num
    rw [tsum_geometric_of_abs_lt_one hh2]
    ring
  rw [h1, h2]
  -- r = 3/103, so r/1-r = (3/103) / (100/103) = 3/100 = 0.03
  have h3: r/(1-r) = 0.03 := by
    rw [r_def]; norm_num
  -- half of 0.03 is 0.015
  rw [h3]; ring