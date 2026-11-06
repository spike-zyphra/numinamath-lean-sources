import Mathlib

theorem algebra_310715 {a b c : ℝ} (ha : |a| + a = 0) (hb : |a * b| = a * b) (hc : |c| - c = 0) :
    Real.sqrt (b^2) - |a + b| - Real.sqrt (c^2 - 2 * b * c + b^2) + |a - c| = 2 * c - b ∨
    Real.sqrt (b^2) - |a + b| - Real.sqrt (c^2 - 2 * b * c + b^2) + |a - c| = b := by
  have ha1 : a ≤ 0 := by
    cases' abs_cases a with ha2 ha2
    · linarith
    · linarith
  have hc1 : c ≥ 0 := by
    cases' abs_cases c with hc2 hc2
    · linarith
    · linarith
  by_cases ha2 : a < 0
  · -- Case a < 0. Then b ≤ 0.
    have h2 : b ≤ 0 := by
      by_contra h
      push_neg at h
      have h4 : a * b < 0 := by nlinarith [show a < 0 by assumption, h]
      have h5 : |a * b| = - (a * b) := by
        rw [abs_of_neg (by nlinarith [h4])]
      have h6 : |a * b| = a * b := by
        linarith [hb]
      rw [h5] at h6
      nlinarith
    -- Real.sqrt (b ^ 2) = -b since b ≤ 0
    have h1 : Real.sqrt (b ^ 2) = -b := by
      have h5 : Real.sqrt (b ^ 2) = abs b := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h5]
      rw [abs_of_nonpos (show b ≤ 0 by nlinarith [h2])]
      all_goals linarith
    have h3 : |a + b| = - (a + b) := by
      have h4 : a + b ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos (show a + b ≤ 0 by linarith [h4])]
      all_goals linarith
    -- sqrt (c ^ 2 - 2bc + b^2) = c - b
    have h4 : Real.sqrt (c ^ 2 - 2 * b * c + b ^ 2) = c - b := by
      have h_eq : c ^ 2 - 2 * b * c + b ^ 2 = (c - b) ^ 2 := by
        ring
      rw [h_eq]
      have h5 : Real.sqrt ((c - b) ^ 2) = abs (c - b) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h5]
      have h8 : c - b ≥ 0 := by
        nlinarith [hc1, h2]
      rw [abs_of_nonneg (show c - b ≥ 0 by linarith)]
      all_goals linarith
    have h5 : |a - c| = c - a := by
      have h6 : a - c ≤ 0 := by
        nlinarith [ha1, hc1]
      rw [abs_of_nonpos (show a - c ≤ 0 by linarith [h6])]
      all_goals nlinarith
    -- Now compute the original expression
    have eq1 : Real.sqrt (b^2) - |a + b| - Real.sqrt (c^2 - 2 * b * c + b^2) + |a - c| = b := by
      rw [h1, h3, h4, h5]
      all_goals
        nlinarith
    right
    linarith [eq1]
  · -- Case a ≥ 0, so a = 0
    have ha3 : a = 0 := by
      linarith
    have h1 : Real.sqrt (b ^ 2) = abs b := by
      rw [Real.sqrt_sq_eq_abs]
    -- sqrt (c ^ 2 - 2bc + b^2) = |c - b|
    have h4 : Real.sqrt (c ^ 2 - 2 * b * c + b ^ 2) = abs (c - b) := by
      have h_eq : c ^ 2 - 2 * b * c + b ^ 2 = (c - b) ^ 2 := by
        ring
      rw [h_eq]
      rw [Real.sqrt_sq_eq_abs]
    -- |a + b| = |b| 
    have h6 : |a + b| = |b| := by
      rw [show a + b = b by
        nlinarith [ha3]
      ]
    -- |a - c| = |(0 : ℝ) - c| = |c| = c
    have h7 : |a - c| = c := by
      rw [show a - c = (0 : ℝ) - c by
        nlinarith [ha3]
      ]
      rw [abs_of_nonpos (show (0 : ℝ) - c ≤ 0 by
        linarith [hc1]
      )
      ]
      all_goals linarith
      all_goals linarith
    by_cases hb2 : b ≥ 0
    · -- Case b ≥ 0.
      have h3 : abs b = b := by
        rw [abs_of_nonneg (show b ≥ 0 by linarith [hb2])]
      by_cases h9 : c ≥ b
      · -- Case c ≥ b. Then |c - b| = c - b
        have h8 : abs (c - b) = c - b := by
          rw [abs_of_nonneg (show c - b ≥ 0 by linarith [h9])]
        have eq1 : Real.sqrt (b^2) - |a + b| - Real.sqrt (c^2 - 2 * b * c + b^2) + |a - c| = b := by
          rw [h1, h4, h6, h7]
          rw [h3, h8]
          all_goals
            nlinarith
        right
        linarith [eq1]
      · -- Case c < b. Then |c - b| = b - c
        have h8 : abs (c - b) = b - c := by
          rw [abs_of_neg (show c - b < 0 by nlinarith [show ¬(c ≥ b) by tauto, hb2, hc1]
          )
          ]
          <;> try { nlinarith }
          <;> try { tauto }
        have eq1 : Real.sqrt (b^2) - |a + b| - Real.sqrt (c^2 - 2 * b * c + b^2) + |a - c| = 2 * c - b := by
          rw [h1, h4, h6, h7]
          rw [h3, h8]
          all_goals
            nlinarith
        left
        linarith [eq1]
    · -- Case b < 0.
      have hb3 : b < 0 := by
        linarith
      have h3 : abs b = -b := by
        rw [abs_of_neg (show b < 0 by linarith [hb3])]
      have h8 : abs (c - b) = c - b := by
        have h9 : c - b ≥ 0 := by
          nlinarith [hc1, hb3]
        rw [abs_of_nonneg (show c - b ≥ 0 by linarith [h9])]
        all_goals linarith
      have eq1 : Real.sqrt (b^2) - |a + b| - Real.sqrt (c^2 - 2 * b * c + b^2) + |a - c| = b := by
        rw [h1, h4, h6, h7]
        rw [h3, h8]
        all_goals
          nlinarith
      right
      linarith [eq1]
  all_goals linarith
  all_goals linarith