import Mathlib

theorem algebra_191206 (t : ℝ) (ht : t ∈ Set.Icc 0 2) :
    dist (40 * t) (16 * t ^ 2 + 9) ≤ 16 := by
  rcases ht with ⟨ht0, ht2⟩
  have h3 : dist (40 * t) (16 * t ^ 2 + 9) = |40 * t - (16 * t ^ 2 + 9)| := by
    simp [dist]
    <;> ring_nf <;> norm_num
  rw [h3]
  have h4 : -16 ≤ 40 * t - (16 * t ^ 2 + 9) ∧ 40 * t - (16 * t ^ 2 + 9) ≤ 16 := by
    constructor
    · -- Prove -16 ≤ 40 * t - (16 * t ^ 2 + 9)
      nlinarith [sq_nonneg (t - 5 / 4), sq_nonneg (t - 0), sq_nonneg (t - 2)]
    · -- Prove 40 * t - (16 * t ^ 2 + 9) ≤ 16
      nlinarith [sq_nonneg (t - 5 / 4), sq_nonneg (t - 0), sq_nonneg (t - 2)]
  apply abs_le.mpr
  constructor <;> nlinarith