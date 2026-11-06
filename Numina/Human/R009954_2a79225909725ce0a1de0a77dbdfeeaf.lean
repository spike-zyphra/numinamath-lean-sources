import Mathlib

/- Is the number

$$
\left(1+\frac{1}{2}\right)\left(1+\frac{1}{4}\right)\left(1+\frac{1}{6}\right) \ldots\left(1+\frac{1}{2018}\right)
$$

greater than, less than, or equal to 50 ? -/
theorem algebra_609847: ∏ i ∈ Finset.range 1009, ((1:ℝ) + 1 / (2 * i + 2)) < 50 := by
  let s := ∏ i ∈ Finset.range 1009, ((1:ℝ) + 1 / (2 * i + 2))
  let s' := ∏ i ∈ Finset.range 1009, ((1:ℝ) + 1 / (2 * i + 1))
  -- prove s < s'
  have h1: s < s' := by
    apply Finset.prod_lt_prod
    . intro i hi
      apply add_pos zero_lt_one
      apply div_pos zero_lt_one
      linarith
    . intro i hi
      apply add_le_add_left
      rw [one_div, one_div, inv_le_inv₀]
      simp
      linarith
      linarith
    . use 0
      simp
      rw [<-sub_lt_zero]
      ring_nf
      apply div_neg_of_neg_of_pos (by norm_num) (by norm_num)
  -- each item of s is positive, so s is positive
  have h2: 0 < s := by
    apply Finset.prod_pos
    intro i hi
    apply add_pos zero_lt_one
    apply div_pos zero_lt_one
    linarith
  -- prove s * s < s * s'
  have h3: s * s < s * s' := mul_lt_mul_of_pos_left h1 h2
  -- we can calculate s * s' by induction
  have h4 {n: ℕ}: (∏ i ∈ Finset.range n, ((1:ℝ) + 1 / (2 * i + 2))) * (∏ i ∈ Finset.range n, ((1:ℝ) + 1 / (2 * i + 1))) = 2 * n + 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc _ = (∏ x ∈ Finset.range n, ((1:ℝ) + 1 / (2 * x + 2))) * (∏ x ∈ Finset.range n, ((1:ℝ) + 1 / (2 * x + 1))) * (1 + 1 / (2 * ↑n + 2)) * (1 + 1 / (2 * ↑n + 1)) := by ring
           _ = (2 * n + 1) * (1 + 1 / (2 * n + 2)) * (1 + 1 / (2 * n + 1)) := by rw [ih]
           _ = (2 * ↑n + 1) * ((2 * n + 2) / (2 * n + 2) + 1 / (2 * n + 2)) * ((2 * n + 1)/(2 * n + 1) + 1 / (2 * n + 1)) := by rw [div_self, div_self]; linarith; linarith
           _ = (2 * ↑n + 1) / (2 * n + 1) * ((2 * n + 2) / (2 * n + 2)) * (2 * n + 3) := by ring
           _ = 2 * ↑n + 3 := by rw [div_self, div_self]; simp; linarith; linarith
           _ = 2 * ↑(n + 1) + 1 := by simp; ring_nf
  -- so we have s * s' = 2019
  have h5: s * s' = 2019 := by rw [h4]; norm_num

  -- so $s^2 < 2019$
  rw [h5, <-sq] at h3

  -- compare s * s and 50 * 50
  simp only [s] at h2
  rw [
    <-abs_of_pos (show 0 < (50:ℝ) by norm_num),
    <-abs_of_pos h2,
    <-sq_lt_sq,
  ]
  apply lt_trans h3
  norm_num
