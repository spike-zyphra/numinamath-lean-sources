import Mathlib

open Real Set
open scoped Real

theorem algebra_199332 : IsGreatest (range (λ x => 3 * sin x + 4 * cos x)) 5 := by
  constructor
  · -- Show that 5 is in the range
    use Real.arctan (3 / 4)
    have h4 : Real.arctan (3 / 4) = Real.arctan (3 / 4) := by rfl
    have h5 : sin (Real.arctan (3 / 4)) = 3 / 5 := by
      have h10 : sin (Real.arctan (3 / 4)) = 3 / 4 / Real.sqrt (1 + (3 / 4) ^ 2) := by
        rw [sin_arctan]
      have h11 : Real.sqrt (1 + (3 / 4) ^ 2) = 5 / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h10, h11]
      all_goals norm_num
    have h6 : cos (Real.arctan (3 / 4)) = 4 / 5 := by
      have h10 : Real.sqrt (1 + (3 / 4) ^ 2) = 5 / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h11 : cos (Real.arctan (3 / 4)) = 1 / Real.sqrt (1 + (3 / 4) ^ 2) := by
        rw [cos_arctan]
      rw [h11, h10]
      all_goals norm_num
      all_goals field_simp
      all_goals norm_num
    simp only [h5, h6]
    all_goals norm_num
  · -- Show that 5 is the greatest element in the range
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h7 : 3 * sin x + 4 * cos x ≤ 5 := by 
      nlinarith [sq_nonneg (4 * sin x - 3 * cos x), sq_nonneg (sin x - 3 / 5), sq_nonneg (cos x - 4 / 5),
        Real.sin_sq_add_cos_sq x, sq_nonneg (3 * sin x + 4 * cos x - 5)]
    simp at hx ⊢
    linarith [h7, hx]