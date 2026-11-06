import Mathlib

theorem algebra_11334 : {x : ℝ | x ≠ 4 ∧ x * (x + 1) / (x - 4)^2 ≥ 12} = Set.Ico 3 4 ∪ Set.Ioc 4 (64 / 11) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
  constructor
  · -- First direction: if in the left side, then in the right side.
    rintro ⟨h1, h2⟩
    have h5 : x * (x + 1) ≥ 12 * (x - 4) ^2 := by
      have h4 : x * (x + 1) / (x - 4) ^2 ≥ 12 := by
        linarith
      have h6 : x - 4 ≠ 0 := by
        intro h7
        apply h1
        linarith
      have h7 : (x * (x + 1)) / (x - 4) ^2 ≥ 12 := by
        linarith
      have h8 : x * (x + 1) ≥ 12 * (x - 4) ^2 := by
        have h6' : (x - 4 : ℝ) ≠ 0 := h6
        have h5 : (x - 4) ^2 > 0 := by
          exact sq_pos_of_ne_zero h6'
        have h9 : (x * (x + 1) ) / (x - 4) ^2 ≥ 12 := h7
        have h10 : (x * (x + 1) ) ≥ 12 * (x - 4) ^2 := by
          have h11 : (x - 4 : ℝ) ≠ 0 := h6'
          have h5' : (x - 4) ^2 > 0 := by
            exact sq_pos_of_ne_zero h11
          apply (le_div_iff₀ (by
            nlinarith
          )).mp at h9
          linarith
        linarith
      linarith
    have h6 : -11 * x ^2 + 97 * x - 192 ≥ 0 := by
      nlinarith
    have h7 : 11 * x ^2 - 97 * x + 192 ≤ 0 := by
      nlinarith
    have h8 : 3 ≤ x := by nlinarith
    have h9 : x ≤ 64 / 11 := by nlinarith
    by_cases h10 : x < 4
    · -- 3 < x < 4
      left
      constructor <;> linarith
    · -- x ≥ 4
      have h11 : x > 4 := by
        by_contra h
        push_neg at h
        have h12 : x = 4 := by linarith
        contradiction
      right
      constructor
      · -- x > 4
        linarith
      · -- x ≤ 64 / 11
        linarith
  · -- Second direction: if in the right side, then in the left side.
    rintro (h | h)
    · -- x in [3, 4)
      rcases h with ⟨hx1, hx2⟩
      constructor
      · -- x ≠ 4
        linarith
      · -- x * (x + 1) / (x - 4)^2 ≥ 12
        have h1 : x * (x + 1) ≥ 12 * (x - 4) ^2 := by nlinarith
        have h2 : x * (x + 1) / (x - 4) ^2 ≥ 12 := by
          have h6 : x - 4 ≠ 0 := by
            nlinarith
          have h3 : x * (x + 1) ≥ 12 * (x - 4) ^2 := h1
          have h4 : (x * (x + 1)) / (x - 4) ^2 ≥ 12 := by
            have h5 : (x - 4 : ℝ) ^2 > 0 := by
              have h6' : (x - 4 : ℝ) ≠ 0 := h6
              exact sq_pos_of_ne_zero h6'
            apply (le_div_iff₀ h5).mpr
            linarith
          linarith
        linarith
    · -- x in (4, 64/11]
      rcases h with ⟨hx1, hx2⟩
      constructor
      · -- x ≠ 4
        by_contra h
        nlinarith
      · -- x * (x + 1) / (x - 4)^2 ≥ 12
        have h1 : x * (x + 1) ≥ 12 * (x - 4) ^2 := by nlinarith
        have h2 : x * (x + 1) / (x - 4) ^2 ≥ 12 := by
          have h6 : x - 4 ≠ 0 := by
            by_contra h
            nlinarith
          have h3 : x * (x + 1) ≥ 12 * (x - 4) ^2 := h1
          have h4 : (x * (x + 1)) / (x - 4) ^2 ≥ 12 := by
            have h5 : (x - 4 : ℝ) ^2 > 0 := by
              have h6' : (x - 4 : ℝ) ≠ 0 := h6
              exact sq_pos_of_ne_zero h6'
            apply (le_div_iff₀ h5).mpr
            linarith
          linarith
        linarith