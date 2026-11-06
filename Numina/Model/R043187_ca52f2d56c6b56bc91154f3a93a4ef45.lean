import Mathlib

theorem algebra_22519 :
    {x : ℝ | x ≠ 0 ∧ (1 / 2 ≤ (x + 1) / x ∧ (x + 1) / x ≤ 3 / 2)} =
    {x : ℝ | x ≤ -2 ∨ x ≥ 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume x in left set, prove right
    rintro ⟨hx, h1, h2⟩
    by_cases h : x > 0
    · -- Case x > 0
      have h3 : x ≥ 2 := by
        have h2' : (x + 1) / x ≤ 3 / 2 := by linarith
        apply (div_le_iff₀ (by linarith)).mp at h2'
        nlinarith
      right
      linarith
    · -- Case x ≤ 0
      have hx2 : x < 0 := by
        by_contra h'
        push_neg at h'
        have : x = 0 := by linarith
        contradiction
      have h1' : x ≤ -2 := by
        have h1' : 1 / 2 ≤ (x + 1) / x := by linarith
        apply (le_div_iff_of_neg' (by linarith)).mp at h1'
        nlinarith
      left
      linarith
  · -- Assume x in right set, prove left
    rintro (h | h)
    · -- Case x ≤ -2
      constructor
      · -- Show x ≠ 0
        by_contra h'
        have : x = 0 := by linarith
        nlinarith
      constructor
      · -- Show 1/2 ≤ (x + 1) / x
        have hx : x < 0 := by linarith
        apply (le_div_iff_of_neg' (by linarith)).mpr
        nlinarith
      · -- Show (x + 1) / x ≤ 3 / 2
        have hx : x < 0 := by linarith
        apply (div_le_iff_of_neg' (by linarith)).mpr
        nlinarith
    · -- Case x ≥ 2
      constructor
      · -- Show x ≠ 0
        by_contra h'
        have : x = 0 := by linarith
        nlinarith
      constructor
      · -- Show 1/2 ≤ (x + 1) / x
        have hx : x > 0 := by linarith
        apply (le_div_iff₀ (by linarith)).mpr
        nlinarith
      · -- Show (x + 1) / x ≤ 3 / 2
        have hx : x > 0 := by linarith
        apply (div_le_iff₀ (by linarith)).mpr
        nlinarith