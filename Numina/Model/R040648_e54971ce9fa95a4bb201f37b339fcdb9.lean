import Mathlib
open Real
theorem algebra_216010:
  {x : ℝ | 0 ≤ 10 - 3 * x ∧ 0 ≤ 4 - 3 * sqrt (10 - 3 * x) ∧ 0 ≤ 4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * x)) ∧ x - 2 = sqrt (4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * x)))} = {3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume the four conditions, prove x = 3
    intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    have h5 : x - 2 ≥ 0 := by
      by_contra h
      push_neg at h
      have h6 : sqrt (4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * x))) < 0 := by nlinarith [h4, h]
      have h7 : sqrt (4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * x))) ≥ 0 := by positivity
      linarith
    -- From h4, we can square both sides:
    -- (x - 2) = Y, so (x - 2)^2 = Y^2 = (4 - 3\sqrt{4 - 3\sqrt{10 - 3x}})
    -- Therefore: (x - 2)^2 = 4 - 3 \sqrt{4 - 3 \sqrt{10 - 3x}}
    -- Therefore: (x - 2)^2 = 4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * x))
    -- which is eq1.
    have eq1 : (x - 2) ^ 2 = 4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * x)) := by
      calc
        (x - 2) ^ 2 = (sqrt (4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * x)))) ^ 2 := by rw [h4]
        _ = 4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * x)) := by
          rw [Real.sq_sqrt]
          all_goals nlinarith
    -- which is h6.
    have h6 : x ≥ 2 := by
      linarith [h5]
    have h7 : sqrt (4 - 3 * sqrt (10 - 3 * x)) = 1 := by
      nlinarith [Real.sqrt_nonneg (4 - 3 * sqrt (10 - 3 * x)), sq_nonneg (sqrt (4 - 3 * sqrt (10 - 3 * x)) - 1), 
          Real.sq_sqrt (show 0 ≤ (4 - 3 * sqrt (10 - 3 * x) : ℝ) by linarith [h2]), 
          sq_nonneg (x - 3), sq_nonneg (sqrt (10 - 3 * x) - 1), 
          Real.sqrt_nonneg (10 - 3 * x), 
          Real.sq_sqrt (show 0 ≤ (10 - 3 * x : ℝ) by linarith)]
    -- which is h8.
    have h8 : sqrt (10 - 3 * x) = 1 := by
      nlinarith [Real.sqrt_nonneg (10 - 3 * x), Real.sq_sqrt (show 0 ≤ (10 - 3 * x : ℝ) by linarith), h7, 
          Real.sqrt_nonneg (4 - 3 * sqrt (10 - 3 * x)), 
          Real.sq_sqrt (show 0 ≤ (4 - 3 * sqrt (10 - 3 * x) : ℝ) by linarith)]
    -- which is x = 3.
    have h9 : x = 3 := by
      nlinarith [Real.sqrt_nonneg (10 - 3 * x), Real.sq_sqrt (show 0 ≤ (10 - 3 * x : ℝ) by linarith), h8]
    linarith
  · -- Show that 3 is in the left side.
    intro h9
    rw [h9]
    constructor
    · norm_num
    constructor
    · -- Show 0 ≤ 4 - 3 * sqrt (10 - 3 * (3 : ℝ))
      have h1 : sqrt (10 - 3 * (3 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      all_goals norm_num
    constructor
    · -- Show 0 ≤ 4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * (3 : ℝ)))
      have h1 : sqrt (10 - 3 * (3 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt (4 - 3 * sqrt (10 - 3 * (3 : ℝ))) = 1 := by
        rw [h1]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      all_goals norm_num
    · -- Show (3 : ℝ) - 2 = sqrt (4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * (3 : ℝ))))
      have h1 : sqrt (10 - 3 * (3 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt (4 - 3 * sqrt (10 - 3 * (3 : ℝ))) = 1 := by
        rw [h1]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h33 : sqrt (4 - 3 * sqrt (4 - 3 * sqrt (10 - 3 * (3 : ℝ)))) = 1 := by
        rw [h2]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h33]