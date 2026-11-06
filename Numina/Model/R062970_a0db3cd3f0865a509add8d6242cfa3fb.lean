import Mathlib

theorem number_theory_286234 :
    IsLeast {n : ℕ | Odd n ∧ ¬∃ x y : ℕ, x > 0 ∧ y > 0 ∧ n = 7 ^ x - 3 * 2 ^ y} 3 := by
  constructor
  · -- Show 3 is in the set
    constructor
    · -- Show 3 is odd
      exact Nat.odd_iff.mpr (by norm_num)
    · -- Show there's no x and y greater than 0 such that 7^x - 3*2^y = 3
      intro h
      rcases h with ⟨x, y, hx, hy, h_eq⟩
      have h1 : 7 ^ x = 3 + 3 * 2 ^ y := by 
        omega
      have h2 : 3 ∣ 7 ^ x := by 
        omega
      have h3 : ¬(3 ∣ 7 ^ x) := by
        have h : ∀ k > 0, ¬ (3 ∣ 7 ^ k) := by
          intro k hk
          have h1 : ∀ k > 0, 7 ^ k % 3 = 1 := by
            intro k hk
            induction k with
            | zero => 
              simp at hk
            | succ k ih =>
              cases k with
              | zero => 
                simp
              | succ k => 
                simp [Nat.add_mod, pow_succ] at ih ⊢
                all_goals omega
          have h2 : 7 ^ k % 3 = 1 := h1 k hk
          have h3 : 3 ∣ 7 ^ k ↔ 7 ^ k % 3 = 0 := Nat.dvd_iff_mod_eq_zero
          rw [h3] at *
          omega
        specialize h x (by omega)
        exact h
      contradiction
  · -- Show 3 is the smallest in the set
    intro n hn
    have h1 : Odd n := hn.1
    have h2 : ¬∃ x y : ℕ, x > 0 ∧ y > 0 ∧ n = 7 ^ x - 3 * 2 ^ y := hn.2
    by_contra h
    push_neg at h
    have h3 : n < 3 := by linarith
    have h4 : n = 1 := by
      interval_cases n <;> tauto
    have h6 : ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ n = 7 ^ x - 3 * 2 ^ y := by 
      use 1, 1 
      simp [show n = 1 by linarith [h4]]
      all_goals omega 
    have h2' := h2 h6 
    exfalso 
    exact h2'