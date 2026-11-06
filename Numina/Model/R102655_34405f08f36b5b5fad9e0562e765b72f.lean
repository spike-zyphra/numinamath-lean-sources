import Mathlib

theorem algebra_2338 {a b : ℝ} (ha : a ≥ 1) (hb : b ≥ 1)
(h : Real.sqrt (a - 1) + (a * b - 2) ^ 2 = 0) :
∑ i ∈ Finset.range 1991, (1 / ((a + i) * (b + i))) = 1991 / 1992 := by

  have h1 : Real.sqrt (a - 1) ≥ 0 := by positivity
  have h2 : (a * b - 2) ^ 2 ≥ 0 := by positivity

  have h3 : Real.sqrt (a - 1) = 0 := by linarith
  have h4 : a - 1 = 0 := by
    rw [Real.sqrt_eq_zero (by linarith)] at h3
    linarith
  have ha1 : a = 1 := by linarith

  have h5 : a * b - 2 = 0 := by
    nlinarith
  have h5' : a * b = 2 := by linarith

  have hb2 : b = 2 := by
    rw [ha1] at h5'
    nlinarith

  rw [ha1, hb2]

  -- Now, the sum becomes $\sum_{i=0}^{1990} \frac{1}{(1 + i)(2 + i)}$.
  -- This sum telescopes to $1 - \frac{1}{1992} = \frac{1991}{1992}$.
  -- Lean can compute this in the norm_num step

  norm_num [Finset.sum_range_succ]
  <;> try { native_decide }