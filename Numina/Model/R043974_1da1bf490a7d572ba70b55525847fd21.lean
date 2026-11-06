import Mathlib

open Real

/- Calculate: $\frac{1}{1+\sqrt{2}}+\frac{1}{\sqrt{2}+\sqrt{3}}+\frac{1}{\sqrt{3}+\sqrt{4}}+\cdots +\frac{1}{\sqrt{2015}+\sqrt{2016}}=$ ___          ___. -/
theorem algebra_7226 : ∑ i ∈ Finset.range 2015, (1 / (sqrt (i + 1) + sqrt (i + 2))) = 12 * sqrt 14 - 1 := by
  have h1 : ∀ i : ℕ, 1 / (sqrt (i + 1) + sqrt (i + 2)) = sqrt (i + 2) - sqrt (i + 1) := by
    intro i
    have h2 : sqrt (i + 1) + sqrt (i + 2) ≠ 0 := by 
      have h3 : sqrt (i + 1) ≥ 0 := Real.sqrt_nonneg (i + 1)
      have h4 : sqrt (i + 2) ≥ 0 := Real.sqrt_nonneg (i + 2)
      by_contra h
      have h5 : sqrt (i + 1) + sqrt (i + 2) = 0 := by linarith
      have h6 : sqrt (i + 1) = 0 := by linarith [show sqrt (i + 2) ≥ 0 by positivity, show sqrt (i + 1) ≥ 0 by positivity]
      have h7 : (i + 1 : ℝ) = 0 := by 
        calc
          (i + 1 : ℝ) = (sqrt (i + 1)) ^ 2 := by rw [Real.sq_sqrt]; linarith
          _ = (0 : ℝ) ^ 2 := by rw [h6]
          _ = (0 : ℝ) := by norm_num
      have h8 : (i : ℝ) = -1 := by linarith
      have h9 : (i : ℝ) ≥ 0 := by positivity
      linarith
    field_simp [h2]
    have h3 : (sqrt (i + 2) - sqrt (i + 1)) * (sqrt (i + 2) + sqrt (i + 1)) = (i + 2 : ℝ) - (i + 1 : ℝ) := by
      calc
        (sqrt (i + 2) - sqrt (i + 1)) * (sqrt (i + 2) + sqrt (i + 1))
          = sqrt (i + 2) ^ 2 - sqrt (i + 1) ^ 2 := by ring
        _ = (i + 2 : ℝ) - (i + 1 : ℝ) := by
          have h4 : sqrt (i + 2) ^ 2 = (i + 2 : ℝ) := Real.sq_sqrt (by linarith)
          have h5 : sqrt (i + 1) ^ 2 = (i + 1 : ℝ) := Real.sq_sqrt (by linarith)
          linarith [h4, h5]
    have h7 : (sqrt (i + 2) - sqrt (i + 1)) / ((i + 2 : ℝ) - (i + 1 : ℝ)) = sqrt (i + 2) - sqrt (i + 1) := by
      have h8 : (i + 2 : ℝ) - (i + 1 : ℝ) = (1 : ℝ) := by
        linarith
      rw [h8]
      all_goals field_simp [h8, h3]
    have h6 : (1 / (sqrt (i + 1) + sqrt (i + 2))) = (sqrt (i + 2) - sqrt (i + 1)) / ((i + 2 : ℝ) - (i + 1 : ℝ)) := by
      field_simp [h2, h3]
      <;> nlinarith [Real.sqrt_nonneg (i + 1), Real.sqrt_nonneg (i + 2), Real.sq_sqrt (show (0 : ℝ) ≤ i + 1 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ i + 2 by linarith)]
    linarith [h6, h7]

  have h8' : ∑ i in Finset.range 2015, (1 / (sqrt (i + 1) + sqrt (i + 2))) =
      ∑ i in Finset.range 2015, (sqrt (i + 2) - sqrt (i + 1)) := by 
    apply Finset.sum_congr 
    · rfl 
    · intro i hi 
      exact h1 i

  have h9' : ∑ i in Finset.range 2015, (sqrt (i + 2) - sqrt (i + 1)) =
      (sqrt (2016 : ℝ) - 1) := by 
    have h10 : ∀ (n : ℕ), ∑ i in Finset.range n, (sqrt (i + 2) - sqrt (i + 1)) =
        sqrt ((n : ℝ) + 1) - 1 := by
      intro n
      induction n with 
      | zero =>
        norm_num
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp [Real.sqrt_nonneg (n + 1 + 1 : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)]
        <;> ring_nf <;> norm_num 
    specialize h10 2015
    norm_num at h10 ⊢ 
    <;> linarith

  have h10' : ∑ i in Finset.range 2015, (1 / (sqrt (i + 1) + sqrt (i + 2))) = 
      (sqrt (2016 : ℝ) - 1) := by 
    rw [h8']
    exact h9'

  have h4 : sqrt (2016 : ℝ) = (12 * sqrt 14) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)]

  rw [h10']
  rw [h4]
  all_goals norm_num