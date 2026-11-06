import Mathlib


lemma lemma_1 (a b : ℝ) : 2 * abs a + 2 * abs b + abs (a + b) ≥ (1 / 3) * (abs (5 * a + 4 * b) + 5 * abs b + 4 * abs a) := by
  by_cases ha : 0 ≤ a
  ·
    rw [abs_of_nonneg ha]
    by_cases hb : 0 ≤ b
    ·
      rw [abs_of_nonneg hb]
      by_cases hab : 0 ≤ a + b
      ·
        rw [abs_of_nonneg hab]
        by_cases h5 : 0 ≤ 5 * a + 4 * b
        ·
          rw [abs_of_nonneg h5]
          linarith
        ·
          rw [abs_of_neg (lt_of_not_ge h5)]
          linarith
      ·
        rw [abs_of_neg (lt_of_not_ge hab)]
        by_cases h5 : 0 ≤ 5 * a + 4 * b
        ·
          rw [abs_of_nonneg h5]
          linarith
        ·
          rw [abs_of_neg (lt_of_not_ge h5)]
          linarith
    ·
      rw [abs_of_neg (lt_of_not_ge hb)]
      by_cases hab : 0 ≤ a + b
      ·
        rw [abs_of_nonneg hab]
        by_cases h5 : 0 ≤ 5 * a + 4 * b
        ·
          rw [abs_of_nonneg h5]
          linarith
        ·
          rw [abs_of_neg (lt_of_not_ge h5)]
          linarith
      ·
        rw [abs_of_neg (lt_of_not_ge hab)]
        by_cases h5 : 0 ≤ 5 * a + 4 * b
        ·
          rw [abs_of_nonneg h5]
          linarith
        ·
          rw [abs_of_neg (lt_of_not_ge h5)]
          linarith
  ·
    rw [abs_of_neg (lt_of_not_ge ha)]
    by_cases hb : 0 ≤ b
    ·
      rw [abs_of_nonneg hb]
      by_cases hab : 0 ≤ a + b
      ·
        rw [abs_of_nonneg hab]
        by_cases h5 : 0 ≤ 5 * a + 4 * b
        ·
          rw [abs_of_nonneg h5]
          linarith
        ·
          rw [abs_of_neg (lt_of_not_ge h5)]
          linarith
      ·
        rw [abs_of_neg (lt_of_not_ge hab)]
        by_cases h5 : 0 ≤ 5 * a + 4 * b
        ·
          rw [abs_of_nonneg h5]
          linarith
        ·
          rw [abs_of_neg (lt_of_not_ge h5)]
          linarith
    ·
      rw [abs_of_neg (lt_of_not_ge hb)]
      by_cases hab : 0 ≤ a + b
      ·
        rw [abs_of_nonneg hab]
        by_cases h5 : 0 ≤ 5 * a + 4 * b
        ·
          rw [abs_of_nonneg h5]
          linarith
        ·
          rw [abs_of_neg (lt_of_not_ge h5)]
          linarith
      ·
        rw [abs_of_neg (lt_of_not_ge hab)]
        by_cases h5 : 0 ≤ 5 * a + 4 * b
        ·
          rw [abs_of_nonneg h5]
          linarith
        ·
          rw [abs_of_neg (lt_of_not_ge h5)]
          linarith


theorem inequalities_3146 (a b c : ℝ) : |a| + |b| + |c| + |a + b| + |b + c| + |c + a| ≥ (|5 * a + 4 * b| + |5 * b + 4 * c| + |5 * c + 4 * a|) / 3 := by

  have h1 : 2 * abs a + 2 * abs b + abs (a + b) ≥ (1 / 3) * (abs (5 * a + 4 * b) + 5 * abs b + 4 * abs a) := by
    apply lemma_1

  have h2 : 2 * abs b + 2 * abs c + abs (b + c) ≥ (1 / 3) * (abs (5 * b + 4 * c) + 5 * abs c + 4 * abs b) := by
    have h2 : 2 * abs b + 2 * abs c + abs (b + c) ≥ (1 / 3) * (abs (5 * b + 4 * c) + 5 * abs c + 4 * abs b) := by
      by_cases hb : 0 ≤ b
      ·
        rw [abs_of_nonneg hb]
        by_cases hc : 0 ≤ c
        ·
          rw [abs_of_nonneg hc]
          by_cases hb2c : 0 ≤ b + c
          ·
            rw [abs_of_nonneg hb2c]
            by_cases h5 : 0 ≤ 5 * b + 4 * c
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
          ·
            rw [abs_of_neg (lt_of_not_ge hb2c)]
            by_cases h5 : 0 ≤ 5 * b + 4 * c
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
        ·
          rw [abs_of_neg (lt_of_not_ge hc)]
          by_cases hb2c : 0 ≤ b + c
          ·
            rw [abs_of_nonneg hb2c]
            by_cases h5 : 0 ≤ 5 * b + 4 * c
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
          ·
            rw [abs_of_neg (lt_of_not_ge hb2c)]
            by_cases h5 : 0 ≤ 5 * b + 4 * c
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
      ·
        rw [abs_of_neg (lt_of_not_ge hb)]
        by_cases hc : 0 ≤ c
        ·
          rw [abs_of_nonneg hc]
          by_cases hb2c : 0 ≤ b + c
          ·
            rw [abs_of_nonneg hb2c]
            by_cases h5 : 0 ≤ 5 * b + 4 * c
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
          ·
            rw [abs_of_neg (lt_of_not_ge hb2c)]
            by_cases h5 : 0 ≤ 5 * b + 4 * c
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
        ·
          rw [abs_of_neg (lt_of_not_ge hc)]
          by_cases hb2c : 0 ≤ b + c
          ·
            rw [abs_of_nonneg hb2c]
            by_cases h5 : 0 ≤ 5 * b + 4 * c
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
          ·
            rw [abs_of_neg (lt_of_not_ge hb2c)]
            by_cases h5 : 0 ≤ 5 * b + 4 * c
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
    linarith

  have h3 : 2 * abs c + 2 * abs a + abs (c + a) ≥ (1 / 3) * (abs (5 * c + 4 * a) + 5 * abs a + 4 * abs c) := by
    have h3 : 2 * abs c + 2 * abs a + abs (c + a) ≥ (1 / 3) * (abs (5 * c + 4 * a) + 5 * abs a + 4 * abs c) := by
      by_cases hc : 0 ≤ c
      ·
        rw [abs_of_nonneg hc]
        by_cases ha : 0 ≤ a
        ·
          rw [abs_of_nonneg ha]
          by_cases hc2a : 0 ≤ c + a
          ·
            rw [abs_of_nonneg hc2a]
            by_cases h5 : 0 ≤ 5 * c + 4 * a
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
          ·
            rw [abs_of_neg (lt_of_not_ge hc2a)]
            by_cases h5 : 0 ≤ 5 * c + 4 * a
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
        ·
          rw [abs_of_neg (lt_of_not_ge ha)]
          by_cases hc2a : 0 ≤ c + a
          ·
            rw [abs_of_nonneg hc2a]
            by_cases h5 : 0 ≤ 5 * c + 4 * a
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
          ·
            rw [abs_of_neg (lt_of_not_ge hc2a)]
            by_cases h5 : 0 ≤ 5 * c + 4 * a
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
      ·
        rw [abs_of_neg (lt_of_not_ge hc)]
        by_cases ha : 0 ≤ a
        ·
          rw [abs_of_nonneg ha]
          by_cases hc2a : 0 ≤ c + a
          ·
            rw [abs_of_nonneg hc2a]
            by_cases h5 : 0 ≤ 5 * c + 4 * a
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
          ·
            rw [abs_of_neg (lt_of_not_ge hc2a)]
            by_cases h5 : 0 ≤ 5 * c + 4 * a
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
        ·
          rw [abs_of_neg (lt_of_not_ge ha)]
          by_cases hc2a : 0 ≤ c + a
          ·
            rw [abs_of_nonneg hc2a]
            by_cases h5 : 0 ≤ 5 * c + 4 * a
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
          ·
            rw [abs_of_neg (lt_of_not_ge hc2a)]
            by_cases h5 : 0 ≤ 5 * c + 4 * a
            ·
              rw [abs_of_nonneg h5]
              linarith
            ·
              rw [abs_of_neg (lt_of_not_ge h5)]
              linarith
    linarith

  linarith [h1, h2, h3]