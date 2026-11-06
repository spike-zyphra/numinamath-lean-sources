import Mathlib

theorem number_theory_319591 :
    IsLeast {n : ℕ | Odd n ∧ ¬∃ x y : ℕ, x > 0 ∧ y > 0 ∧ n = 7 ^ x - 3 * 2 ^ y} 3 := by
  constructor
  · -- Show 3 is in the set
    constructor
    · -- Show that 3 is odd
      exact ⟨1, by norm_num⟩
    · -- Show that 3 cannot be expressed
      intro h
      rcases h with ⟨x, y, hx, hy, heq⟩
      have h1 : x > 0 := hx
      have h2 : y > 0 := hy
      have eq1 : 7 ^ x % 3 = 1 := by
        have h8 : ∀ k : ℕ, (7 : ℕ) ^ (k + 1) % 3 = 1 := by 
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [pow_succ, Nat.mul_mod] at ih ⊢
            all_goals omega
        specialize h8 (x - 1)
        have h9 : x - 1 + 1 = x := by omega
        rw [h9] at h8
        exact h8
      have eq2 : 3 = 7 ^ x - 3 * 2 ^ y := by
        omega
      have h3 : 7 ^ x = 3 + 3 * 2 ^ y := by
        omega
      have h4 : (7 ^ x) % 3 = (3 + 3 * 2 ^ y) % 3 := by
        rw [h3]
      rw [eq1] at h4
      omega
  · -- Show that 3 is minimal
    intro n hn
    rcases hn with ⟨h_odd, h_not_exp⟩
    by_contra h
    push_neg at h
    have h1 : n < 3 := h
    have h2 : n % 2 = 1 := by
      rcases h_odd with ⟨k, hk⟩
      omega
    have : n = 1 := by
      interval_cases n <;> omega
    have h3 : ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ n = 7 ^ x - 3 * 2 ^ y := by
      use 1, 1
      all_goals
      rw [this]
      all_goals norm_num
    contradiction