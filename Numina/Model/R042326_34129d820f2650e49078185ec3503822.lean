import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_291205 :
  {x : ℝ | x ≠ 1 ∧ x ≠ -1 ∧ (x - 1) / (x + 1) > x / (x - 1)} = 
  {x | x < -1} ∪ {x | 1/3 < x ∧ x < 1} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor 
  · -- Assume h: x ≠ 1 ∧ x ≠ -1 ∧ (x - 1) / (x + 1) > x / (x - 1)
    rintro ⟨h1, h2, h3⟩
    have h4 : (x - 1) / (x + 1) - x / (x - 1) > 0 := by linarith
    have h5 : (x - 1) / (x + 1) - x / (x - 1) = (1 - 3 * x) / ((x + 1) * (x - 1)) := by
      field_simp [(show x + 1 ≠ 0 by 
          by_contra h'
          apply h2
          linarith
        ), (show x - 1 ≠ 0 by 
          intro h
          apply h1
          linarith 
        )
      ]
      ring
    rw [h5] at h4 
    have h6 : (1 - 3 * x) / ((x + 1) * (x - 1)) > (0 : ℝ) := h4
    apply div_pos_iff.mp at h6 
    cases h6 with
    | inl h11 => 
      -- either (0 < 1 - 3 * x ∧ 0 < (x + 1) * (x - 1))
      -- or (1 - 3 * x < 0 ∧ (x + 1) * (x - 1) < 0)
      -- Solve x: { 1 - 3 x > 0 and (x + 1)(x - 1) > 0 } ∪ { 1 - 3 x < 0 and (x + 1)(x - 1) < 0 }
      -- This solves to x < -1 ∪ (1/3 < x < 1)
      have h7 : (1 - 3 * x) > 0 := h11.1 
      have h8 : (x + 1) * (x - 1) > 0 := h11.2 
      have h2' : x < -1 := by
        nlinarith 
      left
      linarith 
    | inr h12 => 
      -- either (0 < 1 - 3 * x ∧ 0 < (x + 1) * (x - 1))
      -- or (1 - 3 * x < 0 ∧ (x + 1) * (x - 1) < 0)
      -- Solve x: { 1 - 3 x > 0 and (x + 1)(x - 1) > 0 } ∪ { 1 - 3 x < 0 and (x + 1)(x - 1) < 0 }
      -- This solves to x < -1 ∪ (1/3 < x < 1)
      have h7 : (1 - 3 * x) < 0 := h12.1 
      have h8 : (x + 1) * (x - 1) < 0 := h12.2 
      have h17 : 1/3 < x := by 
        nlinarith 
      have h18 : x < 1 := by 
        nlinarith 
      right 
      constructor <;> linarith
  · -- Assume h ∈ right side
    rintro (h | ⟨h3, h4⟩)
    · -- Assume x < -1 
      have h1 : x < -1 := h 
      -- Show x ≠ 1
      have hne1 : x ≠ 1 := by 
        by_contra h11 
        nlinarith 
      -- Show x ≠ -1
      have hne2 : x ≠ -1 := by 
        by_contra h2 
        linarith 
      have h5 : (x - 1) / (x + 1) > x / (x - 1) := by 
        have h6 : (x - 1) / (x + 1) - x / (x - 1) > (0 : ℝ) := by 
          have h7 : (x - 1) / (x + 1) - x / (x - 1) = (1 - 3 * x) / ((x + 1) * (x - 1)) := by 
            field_simp [(show x + 1 ≠ 0 by 
                nlinarith 
            ), (show x - 1 ≠ 0 by 
                nlinarith 
            )
            ]
            ring 
          rw [h7] 
          have h8 : (1 - 3 * x) / ((x + 1) * (x - 1)) > (0 : ℝ) := by 
            apply div_pos 
            nlinarith 
            nlinarith 
          linarith 
        linarith 
      exact ⟨hne1, hne2, h5⟩ 
    · -- Assume 1/3 < x ∧ x < 1
      have h3' : 1/3 < x := h3 
      have h4' : x < 1 := h4
      -- Show x ≠ 1
      have hne1 : x ≠ 1 := by 
        by_contra h11 
        linarith 
      -- Show x ≠ -1
      have hne2 : x ≠ -1 := by 
        by_contra h2 
        nlinarith 
      have h5 : (x - 1) / (x + 1) > x / (x - 1) := by 
        have h6 : (x - 1) / (x + 1) - x / (x - 1) > (0 : ℝ) := by 
          have h7 : (x - 1) / (x + 1) - x / (x - 1) = (1 - 3 * x) / ((x + 1) * (x - 1)) := by 
            field_simp [(show x + 1 ≠ 0 by 
                nlinarith 
            ), (show x - 1 ≠ 0 by 
                nlinarith 
            )
            ]
            ring 
          rw [h7] 
          have h8 : (1 - 3 * x) / ((x + 1) * (x - 1)) > (0 : ℝ) := by 
            apply div_pos_of_neg_of_neg 
            · -- Show 1 - 3 * x < 0 
              linarith 
            · -- Show (x + 1) * (x - 1) < 0 
              nlinarith 
          linarith 
        linarith 
      exact ⟨hne1, hne2, h5⟩