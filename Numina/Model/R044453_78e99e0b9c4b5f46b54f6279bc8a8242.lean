import Mathlib

open Real

theorem algebra_222290 (a : ℕ → ℝ)
    (ha : ∀ n, a n = 1 / ((n + 1) * sqrt n + n * sqrt (n + 1))) :
    ∑ i in Finset.range 9999, a (i + 1) = 99 / 100 := by
  have h1 : ∀ n : ℕ, a (n + 1) = (1 / sqrt (↑(n) + 1 : ℝ)) - (1 / sqrt (↑(n) + 1 + 1 : ℝ)) := by
    intro n
    have eq2 : a (n + 1) = 1 / ((↑n + 1 + 1 : ℝ) * sqrt (↑n + 1 : ℝ) + (↑n + 1 : ℝ) * sqrt (↑n + 1 + 1 : ℝ)) := by
      specialize ha (n + 1)
      norm_num at ha ⊢
      <;> try { linarith }
    rw [eq2]
    have h2 : sqrt (↑(n) + 1 : ℝ) ≥ 0 := Real.sqrt_nonneg (↑(n) + 1 : ℝ)
    have h3 : sqrt (↑(n) + 1 + 1 : ℝ) ≥ 0 := Real.sqrt_nonneg (↑(n) + 1 + 1 : ℝ)
    field_simp [(show sqrt (↑(n) + 1 : ℝ) ≠ 0 by positivity), (show sqrt (↑(n) + 1 + 1 : ℝ) ≠ 0 by positivity)]
    <;> nlinarith [Real.sqrt_nonneg (↑(n) + 1 : ℝ), Real.sqrt_nonneg (↑(n) + 1 + 1 : ℝ),
        sq_nonneg (sqrt (↑(n) + 1 : ℝ) - sqrt (↑(n) + 1 + 1 : ℝ)),
        Real.sq_sqrt (show (0 : ℝ) ≤ (↑(n) + 1 : ℝ) by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (↑(n) + 1 + 1 : ℝ) by positivity),
        mul_nonneg (Real.sqrt_nonneg (↑(n) + 1 : ℝ)) (Real.sqrt_nonneg (↑(n) + 1 + 1 : ℝ))
      ]
  have h2 : ∀ (n : ℕ), ∑ i in Finset.range n, a (i + 1) = (1 : ℝ) - (1 / sqrt ((↑n : ℝ) + 1 : ℝ)) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [h1 n]
      field_simp [(show sqrt (↑n + 1 : ℝ) ≠ 0 by positivity), (show sqrt (↑n + 1 + 1 : ℝ) ≠ 0 by positivity)]
      <;> nlinarith [Real.sqrt_nonneg (↑n + 1 : ℝ), Real.sqrt_nonneg (↑n + 1 + 1 : ℝ),
          Real.sq_sqrt (show (0 : ℝ) ≤ (↑n + 1 : ℝ) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (↑n + 1 + 1 : ℝ) by positivity),
          sq_nonneg (sqrt (↑n + 1 : ℝ) - sqrt (↑n + 1 + 1 : ℝ)), 
          mul_nonneg (Real.sqrt_nonneg (↑n + 1 : ℝ)) (Real.sqrt_nonneg (↑n + 1 + 1 : ℝ))
        ]
  have h3 := h2 9999
  rw [h3]
  have h4 : sqrt (↑(9999 : ℕ) + 1 : ℝ) = (100 : ℝ) := by
    have h5 : sqrt (↑(9999 : ℕ) + 1 : ℝ) = sqrt (10000 : ℝ) := by 
      norm_num
    rw [h5]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h4]
  all_goals norm_num