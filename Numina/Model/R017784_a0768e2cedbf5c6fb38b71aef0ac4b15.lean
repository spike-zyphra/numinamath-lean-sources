import Mathlib

theorem number_theory_208224 (n : ℕ) (hn : n = 150) :
    IsLeast {x | ∃ k, x = 1 / (2 * 3 ^ (n - k))} (1 / (2 * 3 ^ 49)) := by
  rw [hn]
  constructor
  · -- Show that 1 / (2 * 3 ^ 49) is in the set
    use 101
    all_goals norm_num 
  · -- Show that 1 / (2 * 3 ^ 49) is the least in the set
    intro x hx 
    rcases hx with ⟨k, hk⟩ 
    by_contra h
    push_neg at h
    -- We have $1 / (2 * 3 ^ (150 - k)) < 1 / (2 * 3 ^ 49)$
    have h1 : 1 / (2 * 3 ^ (150 - k)) < 1 / (2 * 3 ^ 49) := by 
      linarith [h, hk]
    -- Show that $2 * 3 ^ (150 - k) ≥ 2$.
    have h2 : 2 * 3 ^ (150 - k) ≥ 2 := by
      have h3 : 3 ^ (150 - k) ≥ 1 := by
        apply Nat.one_le_pow
        all_goals 
          omega
      omega 
    -- Show that $2 * 3 ^ 49 ≥ 2$.
    have h3 : 2 * 3 ^ 49 ≥ 2 := by
      have h4 : 3 ^ 49 ≥ 1 := by
        apply Nat.one_le_pow
        all_goals
          omega 
      omega 
    -- In natural numbers division, $1 / D = 0$ if $D \ge 2$.
    have h4 : 1 / (2 * 3 ^ (150 - k)) = 0 := by 
      rw [Nat.div_eq_zero_iff]
      omega
    -- Similarly, $1 / (2 * 3 ^ 49) = 0$.
    have h5 : 1 / (2 * 3 ^ 49) = 0 := by 
      rw [Nat.div_eq_zero_iff]
      all_goals 
        norm_num 
    -- Then $1 / (2 * 3 ^ (150 - k)) < 1 / (2 * 3 ^ 49)$ becomes $0 < 0$.
    rw [h4, h5] at h1
    all_goals 
      omega