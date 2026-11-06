import Mathlib

theorem number_theory_208287 (n : ℕ) (hn : n = 200) :
    IsLeast {x | ∃ k, x = 1 / (4 * 3 ^ (n - k))} (1 / (4 * 3 ^ 65)) := by 
  rw [hn]
  constructor
  · -- Show that 1 / (4 * 3 ^ 65) is in the set
    use 135
    all_goals norm_num
  · -- Show that 1 / (4 * 3 ^ 65) is the least element
    intro x hx
    rcases hx with ⟨k, hk⟩
    have : x = 1 / (4 * 3 ^ (200 - k)) := hk
    have h1 : 1 / (4 * 3 ^ 65) ≤ (1 / (4 * 3 ^ (200 - k)) ) := by
      have h1 : (1 / (4 * 3 ^ 65) ) = 0 := by
        norm_num
      have h2 : (1 / (4 * 3 ^ (200 - k)) ) = 0 := by
        have h21 : 4 * 3 ^ (200 - k) ≥ 2 := by
          have h2 : 3 ^ (200 - k) ≥ 1 := by
            apply Nat.one_le_pow
            all_goals omega
          omega
        have h22 : (1 : ℕ) / (4 * 3 ^ (200 - k)) = 0 := by 
          rw [Nat.div_eq_zero_iff]
          omega
        exact h22
      omega
    linarith [h1, hk]