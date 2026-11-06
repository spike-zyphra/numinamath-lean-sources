import Mathlib

theorem algebra_10451 :
    IsGreatest { z | ∃ a b c d : ℕ,
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
        b ≠ c ∧ b ≠ d ∧
        c ≠ d ∧
        a ∈ [1, 2, 3, 4] ∧
        b ∈ [1, 2, 3, 4] ∧
        c ∈ [1, 2, 3, 4] ∧
        d ∈ [1, 2, 3, 4] ∧
        z = a * b + b * c + c * d + d * a } 25 := by
  constructor
  · -- Show 25 is in the set
    use 1, 2, 4, 3
    simp
    all_goals norm_num
  · -- Show no value greater than 25 is in the set.
    intro z hz
    rcases hz with ⟨a, b, c, d, hneq1, hneq2, hneq3, hneq4, hneq5, hneq6, ha, hb, hc, hd, hz⟩
    simp at ha hb hc hd
    have h3 : a * b + b * c + c * d + d * a = (a + c) * (b + d) := by
      ring
    have h1 : a * b + b * c + c * d + d * a ≤ 25 := by
      rw [h3]
      have h4 : (a + c : ℕ) + (b + d : ℕ) = 10 := by
        omega
      have h7 : (a + c : ℕ) * (b + d : ℕ) ≤ 25 := by
        have h8 : (a + c : ℕ) + (b + d : ℕ) = 10 := by
          omega
        have h9 : (a + c : ℕ) ≤ 10 := by
          omega
        interval_cases h : (a + c : ℕ) <;> omega
      linarith
    linarith