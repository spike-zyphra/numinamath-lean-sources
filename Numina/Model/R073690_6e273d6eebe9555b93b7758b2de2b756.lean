import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_326607 :
  IsGreatest {y : ℝ | ∃ x, y = (sin x - 1) * (cos x - 1) / (2 + sin (2 * x))} 1 := by
  constructor
  · -- Show that 1 is in the set
    use Real.pi
    have hsin : sin Real.pi = 0 := Real.sin_pi
    have hcos : cos Real.pi = -1 := Real.cos_pi
    have hsin2pi : sin (2 * Real.pi) = 0 := by
      rw [show 2 * Real.pi = (2 : ℝ) * Real.pi by ring]
      rw [Real.sin_two_pi]
      <;> norm_num
    rw [hsin, hcos, hsin2pi]
    norm_num
  · -- Show that for any y in the set, y ≤ 1
    intro y
    rintro ⟨x, hx⟩
    have h1 : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [h1] at hx
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h5 : (sin x - 1) * (cos x - 1) ≤ 2 + 2 * sin x * cos x := by 
      nlinarith [sq_nonneg (sin x + cos x - 1), sq_nonneg (sin x - cos x), sq_nonneg (sin x + 1), sq_nonneg (cos x + 1), Real.sin_sq_add_cos_sq x]
    have h6 : (sin x - 1) * (cos x - 1) / (2 + 2 * sin x * cos x) ≤ 1 := by 
      have h7 : 2 + 2 * sin x * cos x > 0 := by 
        nlinarith [Real.sin_sq_add_cos_sq x, neg_one_le_sin (2 * x), sin_le_one (2 * x)]
      apply (div_le_iff' (by linarith)).mpr
      nlinarith [h5]
    linarith [hx, h6]