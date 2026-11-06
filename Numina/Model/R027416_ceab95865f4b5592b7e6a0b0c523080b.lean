import Mathlib

theorem algebra_12117 {a : ℝ} (A B : Set (ℝ × ℝ))
    (hA : A = {(x, y) | x + a^2 * y + 6 = 0})
    (hB : B = {(x, y) | (a - 2) * x + 3 * a * y + 2 * a = 0})
    (hAB : A ∩ B = ∅) :
    a = 0 ∨ a = -1 := by

  by_contra h
  push_neg at h

  have h1 : a ≠ 0 := by
    intro ha
    have h2 : a = 0 := by linarith
    tauto

  have h2 : a ≠ -1 := by
    intro ha
    have h3 : a = -1 := by linarith
    tauto

  have h3 : A ∩ B = ∅ := hAB

  have h4 : ∃ p, p ∈ A ∩ B := by

    by_cases h3' : a = 3
    · -- a = 3
      have h3' : a = 3 := h3'
      use (-6, 0)
      constructor
      · -- Show in A
        rw [hA]
        simp [h3']
        <;> norm_num
      · -- Show in B
        rw [hB]
        simp [h3']
        <;> norm_num

    · -- a ≠ 3
      have ha3 : a ≠ 3 := by
        intro ha
        apply h3'
        linarith

      have h5 : a + 1 ≠ 0 := by
        intro ha
        apply h2
        linarith

      have h6 : a ≠ 0 := h1

      use (-2 * (a + 3) / (a + 1), -4 / (a * (a + 1)))
      constructor
      · -- Show in A
        rw [hA]
        simp
        field_simp [show a ≠ 0 by exact h1, show a + 1 ≠ 0 by intro h4; apply h2; linarith]
        ring_nf
      · -- Show in B
        rw [hB]
        simp
        field_simp [show a ≠ 0 by exact h1, show a + 1 ≠ 0 by intro h4; apply h2; linarith]
        ring_nf

  have h4' : A ∩ B = ∅ := h3
  rw [h4'] at h4
  simp at h4