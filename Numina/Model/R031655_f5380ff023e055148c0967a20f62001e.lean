import Mathlib

theorem algebra_14123 : {x : ℝ | x ≠ 5 / 2 ∧ 3 ≤ x / (2 * x - 5) ∧ x / (2 * x - 5) < 8} = Set.Ioc (8 / 3) 3 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioc]
  constructor
  · -- Assume x in {x : ℝ | x ≠ 5 / 2 ∧ 3 ≤ x / (2 * x - 5) ∧ x / (2 * x - 5) < 8}
    rintro ⟨hx1, h1, h2⟩
    have h3 : 2 * x - 5 < 0 ∨ 2 * x - 5 > 0 := by
      by_contra h
      push_neg at h
      have h4 : 2 * x - 5 = 0 := by linarith
      have h5 : 2 * x = 5 := by linarith
      have h6 : x = 5 / 2 := by linarith
      tauto
    rcases h3 with (h3 | h3)
    · -- Case where 2 * x - 5 < 0
      have h4 : x < (5 : ℝ) / 2 := by linarith
      have h5 : x ≤ 3 * (2 * x - 5) := by
        have hx10 : 2 * x - 5 < 0 := h3
        have h9 : x / (2 * x - 5) ≥ 3 := by linarith
        have h12 : x ≤ 3 * (2 * x - 5) := by
          have hx100 : 2 * x - 5 < 0 := hx10
          apply (le_div_iff_of_neg' hx100).mp at h9
          nlinarith
        linarith
      have h6 : x ≥ (3 : ℝ) := by
        nlinarith
      linarith
    · -- Case where 2 * x - 5 > 0
      have hx2 : x > (5 : ℝ) / 2 := by linarith
      constructor
      · -- Show that 8/3 < x
        have h4 : 3 * (2 * x - 5) ≤ x := by
          have pos1 : 2 * x - 5 > 0 := h3
          apply (le_div_iff₀ pos1).mp at h1
          linarith
        have h5 : x < 8 * (2 * x - 5) := by
          have pos1 : 2 * x - 5 > 0 := h3
          apply (div_lt_iff₀ pos1).mp at h2
          linarith
        nlinarith
      · -- Show that x ≤ 3
        have h4 : 3 * (2 * x - 5) ≤ x := by
          have pos1 : 2 * x - 5 > 0 := h3
          apply (le_div_iff₀ pos1).mp at h1
          linarith
        nlinarith
  · -- Show that Set.Ioc (8 / 3) 3 ⊆ {x : ℝ | x ≠ 5 / 2 ∧ 3 ≤ x / (2 * x - 5) ∧ x / (2 * x - 5) < 8}
    rintro ⟨h1, h2⟩
    constructor
    · -- Show x ≠ 5 / 2
      linarith
    constructor
    · -- Show 3 ≤ x / (2 * x - 5)
      have hx1 : x > 5 / 2 := by
        nlinarith
      have hx2 : 2 * x - 5 > 0 := by
        nlinarith
      have h4 : 3 * (2 * x - 5) ≤ x := by
        nlinarith
      have pos1 : 2 * x - 5 > 0 := hx2
      apply (le_div_iff₀ pos1).mpr
      linarith
    · -- Show x / (2 * x - 5) < 8
      have hx1 : x > 5 / 2 := by
        nlinarith
      have hx2 : 2 * x - 5 > 0 := by
        nlinarith
      have h5 : x < 8 * (2 * x - 5) := by
        nlinarith
      have pos1 : 2 * x - 5 > 0 := hx2
      apply (div_lt_iff₀ pos1).mpr
      linarith