import Mathlib

theorem number_theory_5843 :
    IsLeast {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ x = (15 * a + 16 * b)^2 ∧ x = (16 * a - 15 * b)^2} ((13 * 37)^2) := by
  constructor
  · -- First, we show that (13 * 37)^2 is indeed in the set.
    use 31, 1
    all_goals norm_num
  · -- Now, we show that (13 * 37)^2 is the smallest such value.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx1, hx2⟩
    by_contra h
    push_neg at h
    have h1 : (15 * a + 16 * b : ℕ) ^2 = (16 * a - 15 * b : ℕ) ^2 := by
      linarith [hx1, hx2]
    have h2 : (15 * a + 16 * b : ℕ) = (16 * a - 15 * b : ℕ) := by
      nlinarith
    have h3 : a = 31 * b := by
      omega
    -- Now substitute a = 31 * b into the expressions, showing they're multiples of (481 * b) ^2
    have h4 : 15 * a + 16 * b = 481 * b := by
      rw [h3]
      omega
    have h5 : (15 * a + 16 * b : ℕ) ^2 = (481 * b) ^2 := by
      rw [h4]
    have h7 : x = (481 * b) ^2 := by
      nlinarith [hx1, h5]
    have h8 : b ≥ 1 := by
      omega
    have h9 : (481 * b) ^2 ≥ (481 * 1) ^2 := by
      have h10 : 481 * b ≥ 481 * 1 := by
        omega
      have h11 : (481 * b) ^2 ≥ (481 * 1) ^2 := by
        nlinarith [h10]
      linarith
    nlinarith [h7, h9, h]