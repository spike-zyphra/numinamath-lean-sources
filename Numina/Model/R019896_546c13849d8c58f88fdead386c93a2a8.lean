import Mathlib

theorem algebra_187453 (f : ℝ → ℝ) (hf : f = fun x => 5 * Real.sin x + 12 * Real.cos x) :
    IsGreatest (Set.image f (Set.univ : Set ℝ)) 13 := by
  constructor
  · -- Show that 13 is in the image of f
    use Real.arcsin (5 / 13)
    rw [hf]
    simp
    have h1 : Real.sin (Real.arcsin (5 / 13 : ℝ)) = (5 / 13 : ℝ) := by
      apply Real.sin_arcsin
      all_goals norm_num
    have h2 : Real.cos (Real.arcsin (5 / 13 : ℝ)) = (12 / 13 : ℝ) := by
      have hcos : Real.cos (Real.arcsin (5 / 13 : ℝ)) = Real.sqrt (1 - (5 / 13 : ℝ) ^ 2) := by 
        rw [Real.cos_arcsin]
      rw [hcos]
      have : Real.sqrt (1 - (5 / 13 : ℝ) ^ 2) = (12 / 13 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      exact this
    simp [h1, h2]
    <;> norm_num
    <;> nlinarith
  · -- Show that 13 is the greatest in the image
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h : 5 * Real.sin x + 12 * Real.cos x ≤ 13 := by
      nlinarith [sq_nonneg (Real.sin x - 5 / 13), sq_nonneg (Real.cos x - 12 / 13),
        Real.sin_sq_add_cos_sq x, sq_nonneg (12 * Real.sin x - 5 * Real.cos x)]
    linarith [h, hx]