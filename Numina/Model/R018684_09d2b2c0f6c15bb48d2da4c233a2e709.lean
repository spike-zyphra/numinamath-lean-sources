import Mathlib

theorem algebra_296093 (x : ℝ) :
    abs (abs (x - 5 / 2) - abs (-3 / 2)) = abs (x ^ 2 - 5 * x + 4) ↔ x = 1 ∨ x = 4 := by
  constructor
  · -- Forward: equation => (x = 1 or x = 4)
    intro h_eq
    have h1 : abs (-3 / 2 : ℝ) = 3 / 2 := by
      norm_num [abs]
    rw [h1] at h_eq
    have h2 : abs (x ^ 2 - 5 * x + 4) = abs (x - 1) * abs (x - 4) := by
      have h3 : x ^ 2 - 5 * x + 4 = (x - 1) * (x - 4) := by
        ring
      rw [h3]
      rw [abs_mul]
    rw [h2] at h_eq
    by_cases h3 : x ≥ 5 / 2
    · -- x ≥ 5 / 2
      have h4 : abs (x - 5 / 2) = x - 5 / 2 := by
        rw [abs_of_nonneg]
        linarith
      have h5 : abs (abs (x - 5 / 2) - 3 / 2) = abs (x - 4) := by
        rw [h4]
        have h5 : (x - 5 / 2 : ℝ) - 3 / 2 = (x - 4 : ℝ) := by
          linarith
        rw [h5]
      rw [h5] at h_eq
      by_cases h40 : abs (x - 4) = 0
      · -- abs (x - 4) = 0 => x = 4
        have hx4 : x = 4 := by
          simp [abs_eq_zero] at h40
          all_goals linarith
        right
        tauto
      · -- abs (x - 4) ≠ 0
        have h31 : abs (x - 1) = 1 := by
          have h400 : abs (x - 1) * abs (x - 4) = abs (x - 4) := by
            nlinarith
          have h401 : abs (x - 1) = 1 := by
            by_cases h402 : abs (x - 4) = 0
            · -- abs (x - 4) = 0
              tauto
            · -- abs (x - 4) ≠ 0
              apply (mul_left_inj' h402).mp
              linarith
          exact h401
        have h32 : (x - 1) = 1 ∨ (x - 1) = -1 := by
          cases eq_or_eq_neg_of_abs_eq h31 with
          | inl h =>
            left
            linarith
          | inr h =>
            right
            linarith
        cases h32 with
        | inl h41 =>
          have hx41 : x = 2 := by linarith
          linarith
        | inr h41 =>
          have hx42 : x = 0 := by linarith
          linarith
    · -- x < 5 / 2
      have h4 : abs (x - 5 / 2) = 5 / 2 - x := by
        rw [abs_of_neg]
        linarith
        all_goals linarith
      have h5 : abs (abs (x - 5 / 2) - 3 / 2) = abs (x - 1) := by
        rw [h4]
        have h6 : (5 / 2 - x : ℝ) - 3 / 2 = (1 - x : ℝ) := by
          nlinarith
        rw [h6]
        rw [show abs (1 - x : ℝ) = abs (x - 1 : ℝ) by
          rw [show (1 - x : ℝ) = - (x - 1 : ℝ) by ring]
          rw [abs_neg]
        ]
      rw [h5] at h_eq
      by_cases h40 : abs (x - 1) = 0
      · -- abs (x - 1) = 0 => x = 1
        have hx1 : x = 1 := by
          simp [abs_eq_zero] at h40
          all_goals linarith
        left
        tauto
      · -- abs (x - 1) ≠ 0
        have h31 : abs (x - 4) = 1 := by
          have h400 : abs (x - 1) * abs (x - 4) = abs (x - 1) := by
            nlinarith
          have h401 : abs (x - 4) = 1 := by
            by_cases h402 : abs (x - 1) = 0
            · -- abs (x - 1) = 0
              tauto
            · -- abs (x - 1) ≠ 0
              apply (mul_left_inj' h402).mp
              linarith
          exact h401
        have h32 : (x - 4) = 1 ∨ (x - 4) = -1 := by
          cases eq_or_eq_neg_of_abs_eq h31 with
          | inl h =>
            left
            linarith
          | inr h =>
            right
            linarith
        cases h32 with
        | inl h41 =>
          have hx41 : x = 5 := by linarith
          linarith
        | inr h41 =>
          have hx42 : x = 3 := by linarith
          linarith
  · -- Backward: (x = 1 or x = 4) => equation
    rintro (h | h)
    · -- x = 1
      rw [h]
      norm_num [abs]
      <;> norm_num
    · -- x = 4
      rw [h]
      norm_num [abs]
      <;> norm_num