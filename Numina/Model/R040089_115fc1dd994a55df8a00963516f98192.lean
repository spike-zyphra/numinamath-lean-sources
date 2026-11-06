import Mathlib

theorem inequalities_67332 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : abs (a - b) ≥ c) (h2 : abs (b - c) ≥ a) (h3 : abs (c - a) ≥ b) :
    a = b + c ∨ b = a + c ∨ c = a + b := by
  by_cases h1' : a ≥ b
  · -- If a ≥ b, then abs (a - b) = a - b
    have h1_eq : abs (a - b) = a - b := by
      rw [abs_of_nonneg]
      linarith
    have h11 : a - b ≥ c := by
      linarith [h1_eq, h1]
    by_cases h2' : b ≥ c
    · -- If b ≥ c, then abs (b - c) = b - c
      have h2_eq : abs (b - c) = b - c := by
        rw [abs_of_nonneg]
        linarith
      have h22 : b - c ≥ a := by
        linarith [h2_eq, h2]
      nlinarith
    · -- If b < c, then abs (b - c) = c - b
      have h2_eq : abs (b - c) = c - b := by
        rw [abs_of_neg]
        linarith
        all_goals linarith
      have h22 : c - b ≥ a := by
        linarith [h2_eq, h2]
      by_cases h3' : c ≥ a
      · -- If c ≥ a, then abs (c - a) = c - a
        have h3_eq : abs (c - a) = c - a := by
          rw [abs_of_nonneg]
          linarith
        have h33 : c - a ≥ b := by
          linarith [h3_eq, h3]
        nlinarith
      · -- If c < a, then abs (c - a) = a - c
        have h3_eq : abs (c - a) = a - c := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        have h33 : a - c ≥ b := by
          linarith [h3_eq, h3]
        nlinarith
  · -- If b > a, then abs (a - b) = b - a
    have h1_eq : abs (a - b) = b - a := by
      rw [abs_of_neg]
      linarith
      all_goals linarith
    have h11 : b - a ≥ c := by
      linarith [h1_eq, h1]
    by_cases h2' : b ≥ c
    · -- If b ≥ c, then abs (b - c) = b - c
      have h2_eq : abs (b - c) = b - c := by
        rw [abs_of_nonneg]
        linarith
      have h22 : b - c ≥ a := by
        linarith [h2_eq, h2]
      by_cases h3' : c ≥ a
      · -- If c ≥ a, then abs (c - a) = c - a
        have h3_eq : abs (c - a) = c - a := by
          rw [abs_of_nonneg]
          linarith
        have h33 : c - a ≥ b := by
          linarith [h3_eq, h3]
        nlinarith
      · -- If c < a, then abs (c - a) = a - c
        have h3_eq : abs (c - a) = a - c := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        have h33 : a - c ≥ b := by
          linarith [h3_eq, h3]
        nlinarith
    · -- If b < c, then abs (b - c) = c - b
      have h2_eq : abs (b - c) = c - b := by
        rw [abs_of_neg]
        linarith
        all_goals linarith
      have h22 : c - b ≥ a := by
        linarith [h2_eq, h2]
      by_cases h3' : c ≥ a
      · -- If c ≥ a, then abs (c - a) = c - a
        have h3_eq : abs (c - a) = c - a := by
          rw [abs_of_nonneg]
          linarith
        have h33 : c - a ≥ b := by
          linarith [h3_eq, h3]
        nlinarith
      · -- If c < a, then abs (c - a) = a - c
        have h3_eq : abs (c - a) = a - c := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        have h33 : a - c ≥ b := by
          linarith [h3_eq, h3]
        nlinarith