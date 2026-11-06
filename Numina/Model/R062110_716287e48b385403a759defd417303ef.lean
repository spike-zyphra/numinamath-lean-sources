import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_289187 {f : ℝ → ℝ}
  (hf : f = λ x => 4^x + 4^(-x) - 2^(x+1) - 2^(1-x) + 5) :
  IsLeast (range f) 3 := by
  constructor
  · -- Prove that 3 is in the range of f.
    use (0 : ℝ)
    simp [hf]
    all_goals norm_num
  · -- Prove that 3 is the least value in the range of f.
    intro y
    rintro ⟨x, hx⟩
    simp [hf] at hx
    have h1 : (4:ℝ) ^ x + (4:ℝ) ^ (-x) - (2:ℝ) ^ (x + 1) - (2:ℝ) ^ (1 - x) + 5 ≥ (3 : ℝ) := by
      have h2 : (4:ℝ) ^ x + (4:ℝ) ^ (-x) - (2:ℝ) ^ (x + 1) - (2:ℝ) ^ (1 - x) + 5 - (3 : ℝ) ≥ 0 := by
        have h3 : (4:ℝ) ^ x + (4:ℝ) ^ (-x) - (2:ℝ) ^ (x + 1) - (2:ℝ) ^ (1 - x) + 5 - (3 : ℝ) =
          (2:ℝ) ^ (2 * x) + (2:ℝ) ^ (-2 * x) - 2 * (2:ℝ) ^ x - 2 * (2:ℝ) ^ (-x) + 2 := by
          have h4 : (4:ℝ) ^ x = (2:ℝ) ^ (2 * x) := by
            rw [show (4 : ℝ) ^ x = (2 ^ (2 : ℝ)) ^ x by norm_num]
            rw [← Real.rpow_mul]
            ring_nf
            norm_num
          have h5 : (4:ℝ) ^ (-x) = (2:ℝ) ^ (-2 * x) := by
            rw [show (4 : ℝ) ^ (-x) = (2 ^ (2 : ℝ)) ^ (-x) by norm_num]
            rw [← Real.rpow_mul]
            ring_nf
            norm_num
          have h6 : (2:ℝ) ^ (x + 1) = (2:ℝ) ^ x * (2:ℝ) ^ (1 : ℝ) := by
            rw [← Real.rpow_add]
            ring_nf
            all_goals norm_num
          have h7 : (2:ℝ) ^ (1 - x) = (2:ℝ) ^ (1 : ℝ) * (2:ℝ) ^ (-x) := by
            rw [← Real.rpow_add]
            ring_nf
            all_goals norm_num
          rw [h4, h5]
          rw [h6, h7]
          norm_num
          <;> ring_nf <;> norm_num
        rw [h3]
        have h4 : (2:ℝ) ^ (2 * x) + (2:ℝ) ^ (-2 * x) - 2 * (2:ℝ) ^ x - 2 * (2:ℝ) ^ (-x) + 2 ≥ 0 := by
          have h5 : (2:ℝ) ^ x > 0 := by positivity
          have h6 : (2:ℝ) ^ (-x) > 0 := by positivity
          have h7 : (2:ℝ) ^ (2 * x) = ((2:ℝ) ^ x) ^ 2 := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul]
            ring_nf
            all_goals norm_num
          have h8 : (2:ℝ) ^ (-2 * x) = ((2:ℝ) ^ (-x)) ^ 2 := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul]
            ring_nf
            all_goals norm_num
          rw [h7, h8]
          nlinarith [sq_nonneg ((2:ℝ) ^ x - 1), sq_nonneg ((2:ℝ) ^ (-x) - 1),
            sq_nonneg ((2:ℝ) ^ x - (2:ℝ) ^ (-x)), 
            mul_pos h5 h6]
        linarith
      linarith
    linarith [h1, hx]