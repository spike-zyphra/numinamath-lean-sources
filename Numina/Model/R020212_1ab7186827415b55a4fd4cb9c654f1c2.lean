import Mathlib

theorem number_theory_166323 (x : ℤ) :
    (∃ a b, a^2 = x^2 + 5 * x + 1 ∧ b^2 = x^2 + 3 * x + 7) ↔ x = 3 := by
  constructor
  · -- If exists integers a and b satisfying the equations, then x = 3
    rintro ⟨a, b, h1, h2⟩
    have h30 : (2 * x + 5 - 2 * a) * (2 * x + 5 + 2 * a) = 21 := by
      nlinarith [h1]
    have h31 : (2 * x + 5 - 2 * a) ∣ 21 := by
      use (2 * x + 5 + 2 * a)
      all_goals
      linarith [h30]
    have h37 : x = 3 ∨ x = 0 ∨ x = -8 ∨ x = -5 := by
      have h38 : (2 * x + 5 - 2 * a) ∣ 21 := h31
      have h39 : (2 * x + 5 - 2 * a) ≤ 21 := by
        exact Int.le_of_dvd (show 0 < (21 : ℤ) by norm_num) h38
      have h40 : (2 * x + 5 - 2 * a) ≥ -21 := by
        have h41 : -(2 * x + 5 - 2 * a) ∣ 21 := by
          exact Int.neg_dvd.2 h38
        have h42 : -(2 * x + 5 - 2 * a) ≤ 21 := by
          exact Int.le_of_dvd (show 0 < (21 : ℤ) by norm_num) h41
        linarith
      interval_cases h43 : (2 * x + 5 - 2 * a) <;> omega
    rcases h37 with (h38 | h38 | h38 | h38)
    · -- x = 3
      omega
    · -- x = 0
      rw [show x = (0 : ℤ) by linarith] at h2
      have h40 : b ^ 2 = 7 := by
        nlinarith
      have h41 : b ≤ 2 := by nlinarith [sq_nonneg (b : ℤ)]
      have h42 : b ≥ -2 := by nlinarith [sq_nonneg (b : ℤ)]
      interval_cases b <;> omega
    · -- x = -8
      rw [show x = (-8 : ℤ) by linarith] at h2
      have h40 : b ^ 2 = 47 := by
        nlinarith
      have h41 : b ≤ 6 := by nlinarith [sq_nonneg (b : ℤ)]
      have h42 : b ≥ -6 := by nlinarith [sq_nonneg (b : ℤ)]
      interval_cases b <;> omega
    · -- x = -5
      rw [show x = (-5 : ℤ) by linarith] at h2
      have h40 : b ^ 2 = 17 := by
        nlinarith
      have h41 : b ≤ 4 := by nlinarith [sq_nonneg (b : ℤ)]
      have h42 : b ≥ -4 := by nlinarith [sq_nonneg (b : ℤ)]
      interval_cases b <;> omega
  · -- x = 3 implies the existence of a and b
    intro h
    rw [show x = 3 by linarith [h]]
    use 5, 5
    all_goals
    norm_num