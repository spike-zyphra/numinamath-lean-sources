import Mathlib
open Real Set
theorem algebra_19296 (h : ℝ → ℝ) (a b : ℝ) (h_def : h = fun t => -4.9 * t ^ 2 + 14 * t - 0.4) : ∃ a b : ℝ, {t : ℝ | h t ≥ 6} = (Icc a b) ∧ b - a = 12 / 7:= by 
  use (4 / 7), (16 / 7)
  constructor
  · -- Show {t | h t ≥ 6} = Icc (4/7) (16/7)
    ext t
    simp [h_def]
    constructor
    · -- Assume h t ≥ 6, show t ∈ Icc (4/7) (16/7)
      intro ht
      have h1 : -4.9 * t ^ 2 + 14 * t - 0.4 ≥ 6 := by 
        linarith
      have h2 : t ≥ 4 / 7 := by
        by_contra h'
        push_neg at h'
        have : -4.9 * t ^ 2 + 14 * t - 0.4 < 6 := by
          nlinarith [sq_nonneg (t - 4 / 7 : ℝ), sq_nonneg (t - 16 / 7 : ℝ)]
        nlinarith
      have h3 : t ≤ 16 / 7 := by
        by_contra h'
        push_neg at h'
        have : -4.9 * t ^ 2 + 14 * t - 0.4 < 6 := by
          nlinarith [sq_nonneg (t - 4 / 7 : ℝ), sq_nonneg (t - 16 / 7 : ℝ)]
        nlinarith
      constructor <;> linarith
    · -- Assume t ∈ Icc (4/7) (16/7), show h t ≥ 6
      rintro ⟨ht1, ht2⟩
      have h1 : -4.9 * t ^ 2 + 14 * t - 0.4 ≥ 6 := by
        nlinarith [sq_nonneg (t - 4 / 7 : ℝ), sq_nonneg (t - 16 / 7 : ℝ)]
      linarith
  · -- Show b - a = 12 / 7
    norm_num
    <;> linarith