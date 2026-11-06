import Mathlib

theorem algebra_252936 (f : ℝ → ℝ) (hf : f = fun x => 4 * (Real.cos x) ^ 3 - 3 * (Real.cos x) ^ 2 - 6 * (Real.cos x) + 5) :
    IsGreatest (Set.range f) (27/4) := by
  constructor
  · -- Show that 27/4 is in the range of f
    use Real.pi * (2 / 3)
    rw [hf]
    have h1 : Real.cos (Real.pi * (2 / 3)) = -1 / 2 := by
      have h3 : Real.pi * (2 / 3) = Real.pi - Real.pi / 3 := by
        ring_nf
      rw [h3]
      rw [Real.cos_pi_sub]
      have h3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
      rw [h3]
      all_goals norm_num
    simp [h1]
    norm_num
  · -- Show that 27/4 is the greatest in the range of f
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h2 : -1 ≤ Real.cos x ∧ Real.cos x ≤ 1 := by
      constructor
      · -- Show that -1 ≤ Real.cos x
        linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
      · -- Show that Real.cos x ≤ 1
        linarith [Real.cos_le_one x]
    nlinarith [sq_nonneg (Real.cos x + 1 / 2), sq_nonneg (Real.cos x - 1), sq_nonneg (Real.cos x - (-1 / 2)), Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x), sq_nonneg (Real.cos x - (-1 / 2)), sq_nonneg (Real.cos x - 1), Real.sin_sq_add_cos_sq x]