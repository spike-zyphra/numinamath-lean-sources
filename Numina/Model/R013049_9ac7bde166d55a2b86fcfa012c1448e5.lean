import Mathlib

theorem algebra_153107 (a b : ℝ) (h₀ : ∑ i ∈ Finset.range 8, |(i + 1) - a| = 612)
    (h₁ : ∑ i ∈ Finset.range 8, |(i + 1) - b| = 240) (h₂ : a + b = 100.5) :
    a = 27 ∨ a = -3 := by
  norm_num [Finset.sum_range_succ] at h₀ h₁
  have h3 : a = 81 ∨ a = -72 := by
    by_cases h9 : a ≥ 8
    · -- If a ≥ 8
      rw [abs_of_nonpos (by linarith : (1 - a : ℝ) ≤ 0), 
          abs_of_nonpos (by linarith : (2 - a : ℝ) ≤ 0), 
          abs_of_nonpos (by linarith : (3 - a : ℝ) ≤ 0), 
          abs_of_nonpos (by linarith : (4 - a : ℝ) ≤ 0), 
          abs_of_nonpos (by linarith : (5 - a : ℝ) ≤ 0), 
          abs_of_nonpos (by linarith : (6 - a : ℝ) ≤ 0), 
          abs_of_nonpos (by linarith : (7 - a : ℝ) ≤ 0), 
          abs_of_nonpos (by linarith : (8 - a : ℝ) ≤ 0) 
          ] at h₀
      have ha_eq_81 : a = 81 := by
        linarith
      left
      nlinarith
    · -- If a < 8
      by_cases h8 : a ≤ 1
      · -- If a ≤ 1
        rw [abs_of_nonneg (by linarith : (1 - a : ℝ) ≥ 0), 
            abs_of_nonneg (by linarith : (2 - a : ℝ) ≥ 0), 
            abs_of_nonneg (by linarith : (3 - a : ℝ) ≥ 0), 
            abs_of_nonneg (by linarith : (4 - a : ℝ) ≥ 0), 
            abs_of_nonneg (by linarith : (5 - a : ℝ) ≥ 0), 
            abs_of_nonneg (by linarith : (6 - a : ℝ) ≥ 0), 
            abs_of_nonneg (by linarith : (7 - a : ℝ) ≥ 0), 
            abs_of_nonneg (by linarith : (8 - a : ℝ) ≥ 0) 
            ] at h₀
        have ha_eq_neg72 : a = -72 := by
          linarith
        right
        nlinarith
      · -- If 1 < a < 8
        by_cases h7 : a ≥ 2
        · -- If 2 ≤ a < 8
          by_cases h6 : a ≥ 3
          · -- If 3 ≤ a < 8
            by_cases h5 : a ≥ 4
            · -- If 4 ≤ a < 8
              by_cases h4 : a ≥ 5
              · -- If 5 ≤ a < 8
                by_cases h3 : a ≥ 6
                · -- If 6 ≤ a < 8
                  by_cases h2 : a ≥ 7
                  · -- If 7 ≤ a < 8
                    rw [abs_of_nonpos (by linarith : (1 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (2 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (3 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (4 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (5 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (6 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (7 - a : ℝ) ≤ 0), 
                        abs_of_nonneg (by linarith : (8 - a : ℝ) ≥ 0) 
                        ] at h₀
                    -- Here we need to reason about contradiction of a value not giving sum 612.
                    linarith
                  · -- If 6 ≤ a <7
                    rw [abs_of_nonpos (by linarith : (1 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (2 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (3 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (4 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (5 - a : ℝ) ≤ 0), 
                        abs_of_nonpos (by linarith : (6 - a : ℝ) ≤ 0), 
                        abs_of_nonneg (by linarith : (7 - a : ℝ) ≥ 0), 
                        abs_of_nonneg (by linarith : (8 - a : ℝ) ≥ 0) 
                        ] at h₀
                    linarith
                · -- If 5 ≤ a <6
                  rw [abs_of_nonpos (by linarith : (1 - a : ℝ) ≤ 0), 
                      abs_of_nonpos (by linarith : (2 - a : ℝ) ≤ 0), 
                      abs_of_nonpos (by linarith : (3 - a : ℝ) ≤ 0), 
                      abs_of_nonpos (by linarith : (4 - a : ℝ) ≤ 0), 
                      abs_of_nonpos (by linarith : (5 - a : ℝ) ≤ 0), 
                      abs_of_nonneg (by linarith : (6 - a : ℝ) ≥ 0), 
                      abs_of_nonneg (by linarith : (7 - a : ℝ) ≥ 0), 
                      abs_of_nonneg (by linarith : (8 - a : ℝ) ≥ 0) 
                      ] at h₀
                  linarith
              · -- If 4 ≤ a <5
                rw [abs_of_nonpos (by linarith : (1 - a : ℝ) ≤ 0), 
                    abs_of_nonpos (by linarith : (2 - a : ℝ) ≤ 0), 
                    abs_of_nonpos (by linarith : (3 - a : ℝ) ≤ 0), 
                    abs_of_nonpos (by linarith : (4 - a : ℝ) ≤ 0), 
                    abs_of_nonneg (by linarith : (5 - a : ℝ) ≥ 0), 
                    abs_of_nonneg (by linarith : (6 - a : ℝ) ≥ 0), 
                    abs_of_nonneg (by linarith : (7 - a : ℝ) ≥ 0), 
                    abs_of_nonneg (by linarith : (8 - a : ℝ) ≥ 0) 
                    ] at h₀
                linarith
            · -- If 3 ≤ a <4
              rw [abs_of_nonpos (by linarith : (1 - a : ℝ) ≤ 0), 
                  abs_of_nonpos (by linarith : (2 - a : ℝ) ≤ 0), 
                  abs_of_nonpos (by linarith : (3 - a : ℝ) ≤ 0), 
                  abs_of_nonneg (by linarith : (4 - a : ℝ) ≥ 0), 
                  abs_of_nonneg (by linarith : (5 - a : ℝ) ≥ 0), 
                  abs_of_nonneg (by linarith : (6 - a : ℝ) ≥ 0), 
                  abs_of_nonneg (by linarith : (7 - a : ℝ) ≥ 0), 
                  abs_of_nonneg (by linarith : (8 - a : ℝ) ≥ 0) 
                  ] at h₀
              linarith
          · -- If 2 ≤ a <3
            rw [abs_of_nonpos (by linarith : (1 - a : ℝ) ≤ 0), 
                abs_of_nonpos (by linarith : (2 - a : ℝ) ≤ 0), 
                abs_of_nonneg (by linarith : (3 - a : ℝ) ≥ 0), 
                abs_of_nonneg (by linarith : (4 - a : ℝ) ≥ 0), 
                abs_of_nonneg (by linarith : (5 - a : ℝ) ≥ 0), 
                abs_of_nonneg (by linarith : (6 - a : ℝ) ≥ 0), 
                abs_of_nonneg (by linarith : (7 - a : ℝ) ≥ 0), 
                abs_of_nonneg (by linarith : (8 - a : ℝ) ≥ 0) 
                ] at h₀
            linarith
        · -- If 1 < a <2
          rw [abs_of_nonpos (by linarith : (1 - a : ℝ) ≤ 0), 
              abs_of_nonneg (by linarith : (2 - a : ℝ) ≥ 0), 
              abs_of_nonneg (by linarith : (3 - a : ℝ) ≥ 0), 
              abs_of_nonneg (by linarith : (4 - a : ℝ) ≥ 0), 
              abs_of_nonneg (by linarith : (5 - a : ℝ) ≥ 0), 
              abs_of_nonneg (by linarith : (6 - a : ℝ) ≥ 0), 
              abs_of_nonneg (by linarith : (7 - a : ℝ) ≥ 0), 
              abs_of_nonneg (by linarith : (8 - a : ℝ) ≥ 0) 
              ] at h₀
          linarith
        all_goals
          try { linarith }
          try { nlinarith }
  cases h3 with
  | inl h3' =>
    -- Substitute a = 81 into h₂ to find b
    have hb : b = 19.5 := by linarith
    -- Substitute b = 19.5 into h₁ to check sum
    rw [hb] at h₁
    norm_num [abs] at h₁
    all_goals
      try { 
        exfalso 
        <;> nlinarith 
      }
  | inr h3' =>
    -- Substitute a = -72 into h₂ to find b
    have hb : b = 172.5 := by linarith
    -- Substitute b = 172.5 into h₁ to check sum
    rw [hb] at h₁
    norm_num [abs] at h₁
    all_goals
      try { 
        exfalso 
        <;> nlinarith 
      }
  all_goals
    try { 
      exfalso 
      <;> nlinarith 
      <;> tauto 
    }