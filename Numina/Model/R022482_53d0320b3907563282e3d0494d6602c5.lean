import Mathlib

theorem inequalities_303196 :
    IsGreatest {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c = 3984 ∧ a * c + b * c = 1993 ∧ x = a * b * c} 3982 := by
  constructor
  · -- Show 3982 is in the set
    use 1991, 2, 1
    all_goals norm_num
  · -- Show it's greatest
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, hx⟩
    have h3 : c * (a + b) = 1993 := by
      linarith [h2]
    have h4 : c ∣ 1993 := by
      use a + b
      linarith [h3]
    have h8 : c = 1 ∨ c = 1993 := by
      have h9 : c ∣ 1993 := h4
      have h10 : c ≤ 1993 := by
        exact Nat.le_of_dvd (by norm_num) h9
      interval_cases c <;> norm_num at h9 ⊢
      all_goals omega
    rcases h8 with h8 | h8
    · -- c = 1
      have h9 : a + b = 1993 := by
        rw [h8] at h3
        have : (a + b) = 1993 := by
          nlinarith
        linarith
      have h10 : b * (a + 1) = 3984 := by
        rw [show c = 1 by linarith [h8] ] at h1
        linarith
      have h12 : b ≤ 1993 := by
        omega
      have hx1 : a * b * c ≤ 3982 := by
        rw [show c = 1 by omega]
        nlinarith [h10, sq_nonneg (a - 1991 : ℤ), sq_nonneg (b - 2 : ℤ)]
      have hx2 : x = a * b * c := by
        linarith [hx]
      nlinarith [hx2, hx1]
    · -- c = 1993
      have h9 : a + b = 1 := by
        rw [h8] at h3
        nlinarith
      omega