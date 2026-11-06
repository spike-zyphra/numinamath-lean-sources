import Mathlib

theorem algebra_187141 : IsGreatest (Set.range (fun x => 6 * Real.sin x + 8 * Real.cos x)) 10 := by
  constructor
  -- Show 10 is in the range
  · -- Use x such that sin x = 3/5, cos x = 4/5
    use Real.arcsin (3 / 5)
    have h1 : Real.sin (Real.arcsin (3 / 5)) = 3 / 5 := by
      apply Real.sin_arcsin
      all_goals norm_num
    have h2 : Real.cos (Real.arcsin (3 / 5)) = 4 / 5 := by
      have h1' : Real.cos (Real.arcsin (3 / 5)) = Real.sqrt (1 - (3 / 5) ^ 2) := by
        rw [Real.cos_arcsin]
      have h2' : Real.sqrt (1 - (3 / 5) ^ 2) = 4 / 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1', h2']
    simp [h1, h2]
    all_goals norm_num
  -- Show that no greater value is in the range
  · -- Show that 10 is indeed the greatest
    intro y
    rintro ⟨x, hx⟩
    simp at hx 
    have h1 : (6 * Real.sin x + 8 * Real.cos x) ≤ 10 := by
      have h2 : (6 * Real.sin x + 8 * Real.cos x) ^ 2 ≤ (10 : ℝ) ^ 2 := by
        have h4 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        nlinarith [sq_nonneg (6 * Real.cos x - 8 * Real.sin x), sq_nonneg (Real.sin x - 3 / 5), sq_nonneg (Real.cos x - 4 / 5), sq_nonneg (8 * Real.sin x - 6 * Real.cos x), Real.sin_sq_add_cos_sq x]
      nlinarith
    linarith [h1, hx]