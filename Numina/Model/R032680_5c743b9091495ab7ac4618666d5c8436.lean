import Mathlib

theorem number_theory_100287 (a b : ℕ) :
    ∃ n, n^2 = 3^a + 4^b ↔ a = 2 ∧ b = 2 := by 
  use 5
  constructor
  · -- Assume 5^2 = 3^a + 4^b, prove a = 2 ∧ b = 2
    intro h
    have h1 : 3^a + 4^b = 25 := by
      norm_num at h ⊢
      omega
    have h2 : a ≤ 3 := by
      by_contra h
      push_neg at h
      have h3 : 3^a ≥ 81 := by
        have h4 : a ≥ 4 := by
          omega
        have h5 : 3^a ≥ 3^4 := by
          apply Nat.pow_le_pow_of_le_right
          norm_num
          all_goals omega
        have h6 : 3^4 = 81 := by
          norm_num
        have h11 : 3^a ≥ 81 := by
          linarith [h5, h6]
        linarith
      have h31 : 4^b ≥ 0 := by positivity
      linarith [h1, h3, h31]
    -- Prove b ≤ 2
    have h4 : b ≤ 2 := by
      by_contra h
      push_neg at h
      have h5 : 4^b ≥ 64 := by
        have h6 : b ≥ 3 := by
          omega
        have h7 : 4^b ≥ 4^3 := by
          apply Nat.pow_le_pow_of_le_right
          norm_num
          all_goals omega
        have h8 : 4^3 = 64 := by
          norm_num
        have h11 : 4^b ≥ 64 := by
          linarith [h7, h8]
        linarith
      have h31 : 3^a ≥ 0 := by positivity
      linarith [h1, h5, h31]
    interval_cases a <;> interval_cases b <;> omega
  · -- Assume a = 2 ∧ b = 2, prove 5^2 = 3^a + 4^b
    rintro ⟨ha, hb⟩
    rw [ha, hb]
    all_goals
      norm_num