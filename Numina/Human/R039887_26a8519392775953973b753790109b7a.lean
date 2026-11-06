import Mathlib

open intervalIntegral Real

theorem calculus_134961 : ∫ x in (-π / 2)..0, 2^8 * (cos x)^8 = 35 * Real.pi := by
  have : ∀ x, 2 ^ 8 * (cos x) ^ 8 = 70 + cos (x * 2) * 112 + cos (x * 6) * 16 + cos (x * 4) * 56 + cos (x * 8) * 2 := by
    intro x; nth_rw 2 [show 8 = 2*4 by simp]
    rw [pow_mul, cos_sq]; ring_nf
    nth_rw 1 [show 4 = 2*2 by simp]; rw [pow_mul, cos_sq]; ring_nf
    nth_rw 1 [show 3 = 2+1 by simp, pow_succ, cos_sq]; ring_nf
    rw [cos_sq, show cos (x*2)*cos (x*4)*32 = 2*cos (x*2)*cos (x*4)*16 by ring]
    rw [two_mul_cos_mul_cos]; ring_nf
    rw [cos_neg]; ring
  have cont1 : Continuous fun x => cos (x * 2) * 112 := by
    apply Continuous.mul; apply Continuous.comp'
    exact continuous_cos; exact continuous_mul_right 2
    exact continuous_const
  have cont2 : Continuous fun x => cos (x * 6) * 16 := by
    apply Continuous.mul; apply Continuous.comp'
    exact continuous_cos; exact continuous_mul_right 6
    exact continuous_const
  have cont3 : Continuous fun x => cos (x * 4) * 56 := by
    apply Continuous.mul; apply Continuous.comp'
    exact continuous_cos; exact continuous_mul_right 4
    exact continuous_const
  have cont4 : Continuous fun x => cos (x * 8) * 2 := by
    apply Continuous.mul; apply Continuous.comp'
    exact continuous_cos; exact continuous_mul_right 8
    exact continuous_const
  rw [integral_congr]
  · have : ∫ (x : ℝ) in (-π / 2)..0, (70 + cos (x * 2) * 112 + cos (x * 6) * 16 +
    cos (x * 4) * 56 + cos (x * 8) * 2) = 35 * π := by
      repeat rw [integral_add]
      simp; ring_nf; repeat rw [sin_neg]
      have := sin_nat_mul_pi 2; simp [mul_comm] at this
      rw [this]; replace this := sin_nat_mul_pi 3
      simp [mul_comm] at this; rw [this]
      replace this := sin_nat_mul_pi 4; simp [mul_comm] at this
      simp [this]; simp
      any_goals apply Continuous.intervalIntegrable
      any_goals assumption
      · apply Continuous.add; exact continuous_const
        assumption
      · repeat apply Continuous.add
        exact continuous_const; all_goals assumption
      · repeat apply Continuous.add
        exact continuous_const; all_goals assumption
    exact this
  intro x _; simp; rw [this]
