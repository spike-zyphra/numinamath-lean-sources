import Mathlib

open Real Set


theorem algebra_9275
    (f : ℝ → ℝ)
    (hf : f = λ x => min (2 - x ^ 2) x) :
    range f = {y | y ≤ 1} := by
  ext y
  simp [hf]
  constructor
  · -- Assume y ∈ range f, prove y ≤ 1
    intro hy
    rcases hy with ⟨x, hx⟩
    by_cases h : 2 - x ^ 2 ≤ x
    · -- Case where 2 - x^2 ≤ x
      have h1 : min (2 - x ^ 2) x = 2 - x ^ 2 := by
        apply min_eq_left
        linarith
      rw [h1] at hx
      nlinarith [sq_nonneg (x - 1)]
    · -- Case where 2 - x^2 > x
      have h2 : min (2 - x ^ 2) x = x := by
        apply min_eq_right
        nlinarith
      rw [h2] at hx
      nlinarith [sq_nonneg (x - 1)]
  · -- Assume y ≤ 1, prove y ∈ range f
    intro hy
    by_cases h1 : y ≤ -2
    · -- Case where y ≤ -2
      use -Real.sqrt (2 - y)
      have h2 : Real.sqrt (2 - (y : ℝ)) ≥ 2 := by
        have h3 : Real.sqrt (2 - (y : ℝ)) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
        have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
          rw [Real.sqrt_eq_cases]
          all_goals norm_num
        nlinarith [h3, h4]
      have h4 : (-Real.sqrt (2 - y)) ^ 2 = Real.sqrt (2 - y) ^ 2 := by 
        ring_nf
      have h5 : Real.sqrt (2 - y) ^ 2 = (2 - (y : ℝ)) := Real.sq_sqrt (by linarith)
      have h6 : 2 - (-Real.sqrt (2 - y) ) ^ 2 = (y : ℝ) := by
        nlinarith [h4, h5]
      by_cases h7 : 2 - (-Real.sqrt (2 - y) ) ^ 2 ≤ (-Real.sqrt (2 - y) : ℝ)
      · -- Case where 2 - (-Real.sqrt (2 - y) ) ^ 2 ≤ -Real.sqrt (2 - y)
        have h8 : min (2 - (-Real.sqrt (2 - y) ) ^ 2) (-Real.sqrt (2 - y) ) = 2 - (-Real.sqrt (2 - y) ) ^ 2 := by
          apply min_eq_left
          linarith
        rw [h8]
        linarith [h6]
      · -- Case where 2 - (-Real.sqrt (2 - y) ) ^ 2 > -Real.sqrt (2 - y)
        have h8 : min (2 - (-Real.sqrt (2 - y) ) ^ 2) (-Real.sqrt (2 - y) ) = -Real.sqrt (2 - y) := by
          apply min_eq_right
          linarith
        rw [h8]
        nlinarith [h4, h5, Real.sqrt_nonneg (2 - (y : ℝ))]
    · -- Case where y > -2
      by_cases h2 : y ≤ 1
      · -- Case where -2 < y ≤ 1
        use (y : ℝ)
        have h3 : min (2 - (y : ℝ) ^ 2) (y : ℝ) = (y : ℝ) := by 
          apply min_eq_right
          nlinarith
        rw [h3]
        all_goals linarith
      · -- Case where y > 1
        linarith