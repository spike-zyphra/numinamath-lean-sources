import Mathlib

theorem algebra_12853 :
{x : ℝ | (x ≠ 1) ∧ (x ≠ -1) ∧ (x ^ 2 / (x + 1) ≥ 2 / (x - 1) + 5 / 4)} =
  Set.Ioo (-1) 1 ∪ Set.Ici 3 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
  constructor
  · -- Assume x satisfies the inequality.
    rintro ⟨hx1, hx2, h⟩
    have h1 : (x ^ 2 / (x + 1) ) - (2 / (x - 1) + 5 / 4) ≥ 0 := by linarith
    have h2 : (x ^ 2 / (x + 1)) - (2 / (x - 1) + 5 / 4) =
        (4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3) / (4 * (x + 1) * (x - 1)) := by
      have h3 : x + 1 ≠ 0 := by
        intro h4
        apply hx2
        linarith
      have h4 : x - 1 ≠ 0 := by
        intro h5
        apply hx1
        linarith
      field_simp [h3, h4]
      ring
    rw [h2] at h1
    have h4 : 4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3 = (x - 3) * (4 * x ^ 2 + 3 * x + 1) := by ring
    have h5 : 4 * x ^ 2 + 3 * x + 1 > 0 := by
      nlinarith [sq_nonneg (x + 3 / 8)]
    have h6 : (4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3) / (4 * (x + 1) * (x - 1)) =
        (x - 3) * (4 * x ^ 2 + 3 * x + 1) / (4 * (x + 1) * (x - 1)) := by rw [h4]
    rw [h6] at h1
    by_cases h7 : x + 1 > 0
    · -- Case x + 1 > 0, so x > -1
      by_cases h8 : x - 1 > 0
      · -- Case x - 1 > 0, so x > 1
        have h9 : x ≥ 3 := by
          apply (div_nonneg_iff).mp at h1
          cases h1 with
          | inl h1l =>
            nlinarith [h5]
          | inr h1r =>
            nlinarith [h5]
        simp [h9]
      · -- Case x - 1 ≤ 0
        have h8 : x - 1 < 0 := by
          by_contra h
          push_neg at h
          have : x - 1 = 0 := by linarith
          have h3 : x = 1 := by linarith
          contradiction
        have h10 : x < 1 := by nlinarith
        have h11 : x > -1 := by nlinarith
        simp [h10, h11]
    · -- Case x + 1 ≤ 0
      have h6 : x + 1 < 0 := by
        by_contra h
        push_neg at h
        have : x + 1 = 0 := by linarith
        have h3 : x = -1 := by linarith
        contradiction
      have h7 : x - 1 < 0 := by nlinarith
      have h8 : x < -1 := by nlinarith
      have h9 : x > -1 := by
        apply (div_nonneg_iff).mp at h1
        cases h1 with
        | inl h1l =>
          nlinarith [h5]
        | inr h1r =>
          nlinarith [h5]
      nlinarith
  · -- Assume x ∈ (-1, 1) ∪ [3, ∞).
    rintro (h | h)
    · -- Case x ∈ (-1, 1)
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Show x ≠ 1
        linarith
      constructor
      · -- Show x ≠ -1
        linarith
      · -- Show the inequality
        have h3 : (x ^ 2 / (x + 1) ) - (2 / (x - 1) + 5 / 4) ≥ 0 := by
          have h31 : (x ^ 2 / (x + 1) ) - (2 / (x - 1) + 5 / 4) =
              (4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3) / (4 * (x + 1) * (x - 1)) := by
            have h4 : x + 1 > 0 := by linarith
            have h5 : x - 1 < 0 := by linarith
            field_simp [(show x + 1 ≠ 0 by linarith), (show x - 1 ≠ 0 by linarith)]
            ring
          rw [h31]
          apply div_nonneg_of_nonpos
          · -- Show $4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3 ≤ 0$
            have h9 : 4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3 = (x - 3) * (4 * x ^ 2 + 3 * x + 1) := by ring
            rw [h9]
            have h10 : x - 3 ≤ 0 := by linarith
            have h5 : 4 * x ^ 2 + 3 * x + 1 > 0 := by
              nlinarith [sq_nonneg (x + 3 / 8)]
            nlinarith
          · -- Show $4 * (x + 1) * (x - 1) ≤ 0$
            nlinarith
        linarith
    · -- Case x ∈ [3, ∞)
      constructor
      · -- Show x ≠ 1
        by_contra h4
        have : x = 1 := by linarith
        nlinarith
      constructor
      · -- Show x ≠ -1
        by_contra h4
        have : x = -1 := by linarith
        nlinarith
      · -- Show the inequality
        have h3 : (x ^ 2 / (x + 1) ) - (2 / (x - 1) + 5 / 4) ≥ 0 := by
          have h31 : (x ^ 2 / (x + 1) ) - (2 / (x - 1) + 5 / 4) =
              (4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3) / (4 * (x + 1) * (x - 1)) := by
            have h4 : x + 1 > 0 := by nlinarith
            have h5 : x - 1 > 0 := by nlinarith
            field_simp [(show x + 1 ≠ 0 by linarith), (show x - 1 ≠ 0 by linarith)]
            ring
          rw [h31]
          apply div_nonneg
          · -- Show $4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3 ≥ 0$
            have h9 : 4 * x ^ 3 - 9 * x ^ 2 - 8 * x - 3 = (x - 3) * (4 * x ^ 2 + 3 * x + 1) := by ring
            rw [h9]
            have h10 : x - 3 ≥ 0 := by linarith
            have h5 : 4 * x ^ 2 + 3 * x + 1 > 0 := by
              nlinarith [sq_nonneg (x + 3 / 8)]
            nlinarith
          · -- Show $4 * (x + 1) * (x - 1) ≥ 0$
            nlinarith
        linarith