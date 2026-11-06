import Mathlib

open Real

/-11.2. Find all solutions of the equation: $\cos ^{2} x+\cos ^{2} 2 x+\cos ^{2} 3 x=1$.-/
theorem algebra_250589 :
  {x : ℝ | cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1} =
    {(2 * k + 1) * π / 2 | k : ℤ} ∪
    {(2 * k + 1) * π / 4 | k : ℤ} ∪
    {(2 * k + 1) * π / 6 | k : ℤ} := by

    have lem1 (x : ℝ) : cos x ^ 2 = (1 + cos (2 * x)) / 2 := by
      rw [cos_two_mul]
      ring

    have lem2 (x : ℝ) : cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1 ↔
      cos x * cos (2 * x) * cos (3 * x) = 0 := by
        rw [lem1 x, lem1 (2 * x)]

        have : (1 + cos (2 * x)) / 2 + (1 + cos (2 * (2 * x))) / 2 + cos (3 * x) ^ 2 =
          (cos (2 * x) + cos (4 * x)) / 2 + cos (3 * x) ^ 2 + 1 := by
            field_simp
            rw [← mul_assoc]
            norm_num
            ring
        rw [this]

        rw [
          cos_add_cos,
          show (2 * x + 4 * x) / 2 = 3 * x by ring,
          show (2 * x - 4 * x) / 2 = -x by ring,
          cos_neg,
          show 2 * cos (3 * x) * cos x / 2 = cos x * cos (3 * x) by ring
        ]

        have : cos x * cos (3 * x) + cos (3 * x) ^ 2 = (cos x + cos (3 * x)) * cos (3 * x) := by ring
        rw [this]

        rw [
          cos_add_cos,
          show (x + 3 * x) / 2 = 2 * x by ring,
          show ((x - 3 * x) / 2) = -x by ring,
          cos_neg,
          show 2 * cos (2 * x) * cos x * cos (3 * x) = 2 * cos x * cos (2 * x) * cos (3 * x) by ring
        ]

        simp

    ext x
    constructor
    · intro xmem
      simp [lem2] at xmem
      rcases xmem with (hx | h2x) | h3x
      · left; left
        apply cos_eq_zero_iff.mp at hx
        obtain ⟨k, hk⟩ := hx
        use k
        linarith
      · left; right
        apply cos_eq_zero_iff.mp at h2x
        obtain ⟨k, hk⟩ := h2x
        use k
        linarith
      · right
        apply cos_eq_zero_iff.mp at h3x
        obtain ⟨k, hk⟩ := h3x
        use k
        linarith

    · intro xmem
      simp [lem2]

      rcases xmem with (hx | h2x) | h3x
      · left; left
        apply cos_eq_zero_iff.mpr
        obtain ⟨k, hk⟩ := hx
        use k, hk.symm
      · left; right
        apply cos_eq_zero_iff.mpr
        obtain ⟨k, hk⟩ := h2x
        use k
        linarith
      · right
        apply cos_eq_zero_iff.mpr
        obtain ⟨k, hk⟩ := h3x
        use k
        linarith
