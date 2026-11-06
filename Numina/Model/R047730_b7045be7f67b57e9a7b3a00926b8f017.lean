import Mathlib

theorem algebra_292846 (k b : ℝ) (h₀ : k ≠ 0) (h₁ : 3 = k * 1 + b)
    (A B : ℝ × ℝ) (hA : A.1 = -b / k) (hB : B.2 = k * 0 + b)
    (hAB : A.1 > 0 ∧ B.2 > 0) :
    (1 / 2) * A.1 * B.2 ≥ 6 := by
  have h2 : b = 3 - k := by linarith
  have hA1 : A.1 = (k - 3) / k := by
    rw [hA]
    rw [h2]
    field_simp [h₀]
    <;> ring
  have hB2 : B.2 = 3 - k := by
    rw [hB]
    rw [h2]
    all_goals linarith
  rw [hA1, hB2]
  have h3 : k < 0 := by
    have hA1_pos : A.1 > 0 := hAB.1
    have hB2_pos : B.2 > 0 := hAB.2
    rw [hA1] at hA1_pos
    rw [hB2] at hB2_pos
    by_contra h
    push_neg at h
    by_cases hk : k > 0
    · -- Assume k > 0
      have h4 : k > 0 := by linarith
      have h5 : (k - 3) / k > 0 := by linarith
      apply div_pos_iff.mp at h5
      cases h5 with
      | inl h6 =>
        linarith
      | inr h7 =>
        linarith
    · -- Assume k ≤ 0
      have hk1 : k = 0 := by
        have h4 : k ≤ 0 := by linarith
        have h5 : k ≥ 0 := by
          by_contra h
          push_neg at h
          have h6 : k < 0 := by linarith
          have h7 : (k - 3) / k > 0 := by linarith
          have h8 : k < 0 := by linarith
          apply div_pos_iff.mp at h7
          cases h7 with
          | inl h9 =>
            nlinarith
          | inr h10 =>
            nlinarith
        have h5 : k = 0 := by linarith
        tauto
      contradiction
  have hk : k < 0 := h3
  have h4 : (1 / 2) * ((k - 3) / k) * (3 - k) ≥ 6 := by
    have h5 : k < 0 := hk
    have h9 : (k + 3) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h14 : (1 / 2) * ((k - 3) * (3 - k) / k) - 6 ≥ 0 := by
      have h16 : (1 / 2) * ((k - 3) * (3 - k) / k) - 6 = ((k - 3) * (3 - k) - 12 * k) / (2 * k) := by
        field_simp
        <;> ring
      rw [h16]
      apply div_nonneg_of_nonpos
      · -- Show that numerator is ≤ 0
        nlinarith [h9]
      · -- Show that denominator is ≤ 0
        nlinarith
    have h15 : (1 / 2) * ((k - 3) / k) * (3 - k) = (1 / 2) * ((k - 3) * (3 - k) / k) := by
      ring
    rw [h15]
    linarith
  linarith