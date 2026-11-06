import Mathlib

theorem algebra_8991 : Set.range (-Real.cos ^ 2 + Real.sin) = {y |-5/4 ≤ y ∧  y ≤ 1} := by
  ext y
  simp [Set.mem_range]
  constructor
  · -- First direction: show that if y in range, then bounds
    rintro ⟨x, hx⟩
    have h1 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq x]
      linarith
    rw [h1] at hx
    have h2 : -1 ≤ Real.sin x ∧ Real.sin x ≤ 1 := Real.sin_mem_Icc x
    constructor
    · -- Show that -5/4 ≤ y
      nlinarith [sq_nonneg (Real.sin x + 1 / 2), sq_nonneg (Real.sin x - 1), sq_nonneg (Real.sin x + 1)]
    · -- Show that y ≤ 1
      nlinarith [sq_nonneg (Real.sin x - 1), sq_nonneg (Real.sin x + 1), sq_nonneg (Real.sin x + 1 / 2)]
  · -- Second direction: show that if bounds hold, then y in range
    rintro ⟨hy1, hy2⟩
    have h3 : ∃ s, -1 ≤ s ∧ s ≤ 1 ∧ s ^ 2 + s - 1 = y := by
      use (-1 + Real.sqrt (1 + 4 * (y + 1))) / 2
      constructor
      · -- Show -1 ≤ s
        nlinarith [Real.sqrt_nonneg (1 + 4 * (y + 1)), Real.sq_sqrt (show 0 ≤ (1 + 4 * (y + 1) : ℝ) by linarith)]
      constructor
      · -- Show s ≤ 1
        nlinarith [Real.sqrt_nonneg (1 + 4 * (y + 1)), Real.sq_sqrt (show 0 ≤ (1 + 4 * (y + 1) : ℝ) by linarith)]
      · -- Show s ^ 2 + s - 1 = y
        nlinarith [Real.sqrt_nonneg (1 + 4 * (y + 1)), Real.sq_sqrt (show 0 ≤ (1 + 4 * (y + 1) : ℝ) by linarith)]
    rcases h3 with ⟨s, hs1, hs2, h_eq⟩
    use Real.arcsin s
    have h4 : Real.sin (Real.arcsin s) = s := by
      apply Real.sin_arcsin
      all_goals linarith
    have h5 : Real.cos (Real.arcsin s) ^ 2 = 1 - s ^ 2 := by
      have h6 : Real.sin (Real.arcsin s) = s := by
        apply Real.sin_arcsin
        all_goals linarith
      have h7 : Real.cos (Real.arcsin s) ^ 2 + Real.sin (Real.arcsin s) ^ 2 = 1 := Real.cos_sq_add_sin_sq (Real.arcsin s)
      rw [h6] at h7
      nlinarith
    rw [show Real.cos (Real.arcsin s) ^ 2 = 1 - s ^ 2 by linarith [h5]]
    nlinarith [h4, h_eq]