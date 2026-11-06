import Mathlib

theorem number_theory_105420 (n p : ℕ) (hp : Nat.Prime p) :
    ∃ m, m^2 = p^2 + 7^n ↔ (p = 3 ∧ n = 1) := by
  use 4
  constructor
  · -- Assume 4^2 = p^2 + 7^n, prove (p = 3 ∧ n = 1)
    intro h
    have eq1 : p ^ 2 + 7 ^ n = 16 := by
      nlinarith
    have h2 : p ≤ 4 := by
      have h3 : p ^ 2 ≤ 16 := by
        have h4 : 7 ^ n ≥ 0 := by positivity
        nlinarith [eq1, h4]
      have h4 : p ≤ 4 := by nlinarith
      exact h4
    have hp2 : p = 2 ∨ p = 3 := by 
      interval_cases p <;> norm_num at hp ⊢ <;> tauto
    rcases hp2 with (r | r)
    · -- case p = 2
      rw [show p = 2 by linarith [r]] at eq1
      have h3 : 7 ^ n = 12 := by
        nlinarith
      have h5 : 7 ^ n ≥ 49 := by 
        have : n ≥ 2 := by
          by_contra h
          push_neg at h
          have : n = 0 ∨ n = 1 := by
            omega
          rcases this with (h | h) 
          · rw [h] at h3
            norm_num at h3
          · rw [h] at h3
            norm_num at h3
        have h7 : 7 ^ n ≥ 7 ^ 2 := by 
          apply Nat.pow_le_pow_of_le_right (by norm_num) this
        norm_num at h7 ⊢
        linarith
      have h6 : 12 ≥ 49 := by
        linarith [h3, h5]
      linarith 
    · -- case p = 3
      rw [show p = 3 by linarith [r]] at eq1
      have h3 : 7 ^ n = 7 := by 
        nlinarith 
      have h4 : n = 1 := by 
        have h5 : 7 ^ n = 7 := by 
          linarith [h3] 
        exact Nat.pow_right_injective (by norm_num) h5 
      constructor
      · -- prove p = 3 
        linarith [r] 
      · -- prove n = 1 
        exact h4 
  · -- Assume (p = 3 ∧ n = 1), prove 4^2 = p^2 + 7^n
    rintro ⟨h_eq1, h_eq2⟩
    rw [h_eq1, h_eq2]
    all_goals
    norm_num