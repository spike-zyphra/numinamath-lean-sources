import Mathlib

theorem algebra_206046 :
  {x : ℝ | -16 ≤ x ∧ x ≤ 16 ∧ (16 + x) ^ ((1 : ℝ) / 4) + (16 - x) ^ ((1 : ℝ) / 4) = 4} = {0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if x in set, then x = 0
    rintro ⟨hx₁, hx₂, heq⟩
    have h1 : (16 + x : ℝ) ^ ((1 : ℝ) / 4) ≥ 0 := by
      apply Real.rpow_nonneg
      linarith
    have h2 : (16 - x : ℝ) ^ ((1 : ℝ) / 4) ≥ 0 := by
      apply Real.rpow_nonneg
      linarith
    have h5 : ((16 + x) ^ ((1 : ℝ) / 4)) ^ 4 = (16 + x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h6 : ((16 - x) ^ ((1 : ℝ) / 4)) ^ 4 = (16 - x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h4 : (16 + x : ℝ) ^ ((1 : ℝ) / 4) + (16 - x : ℝ) ^ ((1 : ℝ) / 4) = 4 := by
      linarith
    have h10 : ( (16 + x : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 = ( (16 - x : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 := by
      nlinarith [sq_nonneg ( (16 + x : ℝ) ^ ((1 : ℝ) / 4) - 2 ), sq_nonneg ( (16 - x : ℝ) ^ ((1 : ℝ) / 4) - 2 ), sq_nonneg ( ( (16 + x : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 - ( (16 - x : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 ), mul_nonneg h1 h2 ]
    have h11 : (16 + x : ℝ) ^ ((1 : ℝ) / 4) = (16 - x : ℝ) ^ ((1 : ℝ) / 4) := by
      nlinarith [sq_nonneg ( (16 + x : ℝ) ^ ((1 : ℝ) / 4) - (16 - x : ℝ) ^ ((1 : ℝ) / 4) ), h10 ]
    have h12 : ( (16 + x : ℝ) ^ ((1 : ℝ) / 4) ) = 2 := by
      nlinarith [ h11, h4, sq_nonneg ( (16 + x : ℝ) ^ ((1 : ℝ) / 4) - 2 ), sq_nonneg ( (16 - x : ℝ) ^ ((1 : ℝ) / 4) - 2 ) ]
    have hx0 : x = 0 := by
      have h14 : (16 + x) = 16 := by
        calc
          (16 + x) = ( (16 + x) ^ ((1 : ℝ) / 4) ) ^ 4 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals linarith
          _ = ( (2 : ℝ) ) ^ 4 := by
            rw [show ( (16 + x : ℝ) ^ ((1 : ℝ) / 4) ) = (2 : ℝ) by nlinarith [h12] ]
          _ = (16 : ℝ) := by
            norm_num
      have h15 : x = 0 := by
        nlinarith
      exact h15
    linarith
  · -- Reverse direction
    intro hx
    rw [hx]
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Check that 0 is a solution.
      have h1 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
        have h2 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
          have h11 : (16 : ℝ) ^ ((1 : ℝ) / 4) = ((2 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
            norm_num
          have h12 : ((2 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
            rw [← Real.rpow_mul]
            norm_num
            all_goals norm_num
          rw [h11, h12]
        linarith
      linarith [h1]