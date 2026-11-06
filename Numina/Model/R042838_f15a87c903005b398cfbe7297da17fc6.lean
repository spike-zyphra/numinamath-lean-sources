import Mathlib

open BigOperators Real Set

theorem inequalities_264875 :
  {x : ℝ | x * (x + 1) / (x - 1) > 3 ∧ x ≠ 1} = {x : ℝ | x > 1} ∧
  {x : ℝ | x * (x + 1) / (x - 1) > 6 ∧ x ≠ 1} = {x : ℝ | (1 < x ∧ x < 2) ∨ x > 3} := by
  constructor
  · -- Prove {x : ℝ | x * (x + 1) / (x - 1) > 3 ∧ x ≠ 1} = {x : ℝ | x > 1}
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
    constructor
    · -- Assume x * (x + 1) / (x - 1) > 3 and x ≠ 1, prove x > 1
      intro h
      rcases h with ⟨h1, hx1⟩
      have h2 : x - 1 > 0 := by
        have h3 : x * (x + 1) / (x - 1) - 3 > 0 := by linarith
        have h4 : x * (x + 1) / (x - 1) - 3 = (x ^ 2 - 2 * x + 3) / (x - 1) := by
          field_simp [(show x - 1 ≠ 0 by
            intro h0
            apply hx1
            linarith
          )
          ]
          ring
        rw [h4] at h3
        have h5 : x ^ 2 - 2 * x + 3 > 0 := by
          nlinarith [sq_nonneg (x - 1)]
        have h6 : x - 1 > 0 := by
          by_contra h7
          push_neg at h7
          have h8 : (x ^ 2 - 2 * x + 3) / (x - 1) ≤ 0 := by
            apply div_nonpos_of_nonneg_of_nonpos
            · linarith [h5]
            · linarith
          linarith
        linarith
      linarith
    · -- Assume x > 1, prove x * (x + 1) / (x - 1) > 3 and x ≠ 1
      intro h
      constructor
      · -- Show x * (x + 1) / (x - 1) > 3
        have h2 : x - 1 > 0 := by linarith
        have h3 : x * (x + 1) / (x - 1) > 3 := by
          have h4 : x * (x + 1) / (x - 1) - 3 > 0 := by
            have h5 : x * (x + 1) / (x - 1) - 3 = (x ^ 2 - 2 * x + 3) / (x - 1) := by
              field_simp [(show x - 1 ≠ 0 by
                intro h0
                have : x = 1 := by linarith
                linarith
              )
              ]
              ring
            rw [h5]
            have h7 : x ^ 2 - 2 * x + 3 > 0 := by
              nlinarith [sq_nonneg (x - 1)]
            have h8 : x - 1 > 0 := by linarith
            apply div_pos
            all_goals linarith
          linarith
        linarith
      · -- Show x ≠ 1
        linarith
  · -- Prove {x : ℝ | x * (x + 1) / (x - 1) > 6 ∧ x ≠ 1} = {x : ℝ | (1 < x ∧ x < 2) ∨ x > 3}
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
    constructor
    · -- Assume x * (x + 1) / (x - 1) > 6 and x ≠ 1, prove (1 < x ∧ x < 2) ∨ x > 3
      intro h
      rcases h with ⟨h1, hx1⟩
      have h2 : x * (x + 1) / (x - 1) - 6 > 0 := by linarith
      have h3 : x * (x + 1) / (x - 1) - 6 = (x ^ 2 - 5 * x + 6) / (x - 1) := by
        field_simp [(show x - 1 ≠ 0 by
          intro h0
          apply hx1
          linarith
        )
        ]
        ring
      rw [h3] at h2
      have h4 : x ^ 2 - 5 * x + 6 = (x - 2) * (x - 3) := by
        ring
      have h5 : (x - 2) * (x - 3) / (x - 1) > 0 := by
        rw [h4] at h2
        linarith
      have h6 : ((x - 2) * (x - 3) > 0 ∧ x - 1 > 0) ∨ ((x - 2) * (x - 3) < 0 ∧ x - 1 < 0) := by
        apply div_pos_iff.mp at h5
        tauto
      rcases h6 with (h7 | h8)
      · -- case where (x - 2) * (x - 3) > 0 and x - 1 > 0
        have h8 : x > 1 := by linarith
        have h9 : (x - 2) * (x - 3) > 0 := by
          nlinarith
        by_cases h10 : x < 2
        · -- case where 1 < x < 2
          left
          constructor <;> linarith
        · -- case where x ≥ 2
          have h11 : x > 3 := by
            nlinarith
          right
          linarith
      · -- case where (x - 2) * (x - 3) < 0 and x - 1 < 0
        nlinarith
    · -- Assume (1 < x ∧ x < 2) ∨ x > 3, prove x * (x + 1) / (x - 1) > 6 and x ≠ 1
      intro h
      rcases h with (h1 | h2)
      · -- case where 1 < x < 2
        have h3 : 1 < x := h1.1
        have h4 : x < 2 := h1.2
        constructor
        · -- Show x * (x + 1) / (x - 1) > 6
          have h2 : x * (x + 1) / (x - 1) - 6 > 0 := by
            have h5 : x * (x + 1) / (x - 1) - 6 = (x ^ 2 - 5 * x + 6) / (x - 1) := by
              field_simp [(show x - 1 ≠ 0 by
                nlinarith
              )
              ]
              ring
            rw [h5]
            have h6 : x ^ 2 - 5 * x + 6 > 0 := by
              nlinarith
            have h7 : x - 1 > 0 := by linarith
            apply div_pos
            all_goals linarith
          linarith
        · -- Show x ≠ 1
          nlinarith
      · -- case where x > 3
        have h3 : x > 3 := h2
        constructor
        · -- Show x * (x + 1) / (x - 1) > 6
          have h2 : x * (x + 1) / (x - 1) - 6 > 0 := by
            have h5 : x * (x + 1) / (x - 1) - 6 = (x ^ 2 - 5 * x + 6) / (x - 1) := by
              field_simp [(show x - 1 ≠ 0 by
                nlinarith
              )
              ]
              ring
            rw [h5]
            have h6 : x ^ 2 - 5 * x + 6 > 0 := by
              nlinarith
            have h7 : x - 1 > 0 := by linarith
            apply div_pos
            all_goals linarith
          linarith
        · -- Show x ≠ 1
          nlinarith