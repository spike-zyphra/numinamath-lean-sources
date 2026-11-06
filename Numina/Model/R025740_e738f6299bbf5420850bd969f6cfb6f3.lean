import Mathlib

open Real Set


theorem algebra_181204 : range (λ x => 5 * sin x - 12 * cos x) = {y | -13 ≤ y ∧ y ≤ 13} := by
  have h1 : ∀ x : ℝ, 5 * sin x - 12 * cos x = 13 * sin (x + arcsin (-12 / 13)) := by
    intro x
    have h2 : sin (x + arcsin (-12 / 13)) = sin x * cos (arcsin (-12 / 13)) + cos x * sin (arcsin (-12 / 13)) := by
      rw [sin_add]
    rw [h2]
    have h3 : cos (arcsin (-12 / 13)) = 5 / 13 := by
      have h4 : cos (arcsin (-12 / 13)) = Real.sqrt (1 - (-12 / 13) ^ 2) := by
        rw [cos_arcsin]
      rw [h4]
      have h5 : Real.sqrt (1 - (-12 / 13 : ℝ) ^ 2) = (5 / 13 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    have h6 : sin (arcsin (-12 / 13)) = -12 / 13 := by
      apply Real.sin_arcsin
      all_goals norm_num
    rw [h3, h6]
    ring
  ext y
  simp only [mem_range, mem_setOf_eq, exists_prop]
  constructor
  · -- Assume y in range, so there exists x such that 5 * sin x - 12 * cos x = y.
    rintro ⟨x, hx⟩
    have h7 : 5 * sin x - 12 * cos x = 13 * sin (x + arcsin (-12 / 13)) := h1 x
    rw [h7] at hx
    have h8 : -1 ≤ sin (x + arcsin (-12 / 13)) ∧ sin (x + arcsin (-12 / 13)) ≤ 1 := by
      constructor
      · apply neg_one_le_sin
      · apply sin_le_one
    constructor
    · linarith [hx, h8.1]
    · linarith [hx, h8.2]
  · -- Assume -13 ≤ y ∧ y ≤ 13, show there exists x such that 5 * sin x - 12 * cos x = y
    rintro ⟨hy1, hy2⟩
    use arcsin (y / 13) - arcsin (-12 / 13)
    have h14 : 5 * sin (arcsin (y / 13) - arcsin (-12 / 13)) - 12 * cos (arcsin (y / 13) - arcsin (-12 / 13)) = 13 * sin ( (arcsin (y / 13) - arcsin (-12 / 13)) + arcsin (-12 / 13) ) := by
      have h1 : ∀ x : ℝ, 5 * sin x - 12 * cos x = 13 * sin (x + arcsin (-12 / 13)) := by
        intro x
        have h2 : sin (x + arcsin (-12 / 13)) = sin x * cos (arcsin (-12 / 13)) + cos x * sin (arcsin (-12 / 13)) := by
          rw [sin_add]
        rw [h2]
        have h3 : cos (arcsin (-12 / 13)) = 5 / 13 := by
          have h4 : cos (arcsin (-12 / 13)) = Real.sqrt (1 - (-12 / 13) ^ 2) := by
            rw [cos_arcsin]
          rw [h4]
          have h5 : Real.sqrt (1 - (-12 / 13 : ℝ) ^ 2) = (5 / 13 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          linarith
        have h6 : sin (arcsin (-12 / 13)) = -12 / 13 := by
          apply Real.sin_arcsin
          all_goals norm_num
        rw [h3, h6]
        ring
      specialize h1 (arcsin (y / 13) - arcsin (-12 / 13))
      ring_nf at h1 ⊢
      linarith
    have h15 : (arcsin (y / 13) - arcsin (-12 / 13)) + arcsin (-12 / 13) = arcsin (y / 13) := by
      ring
    rw [h15] at h14
    have h16 : sin (arcsin (y / 13)) = y / 13 := by
      apply Real.sin_arcsin
      all_goals
      linarith
    rw [h16] at h14
    linarith