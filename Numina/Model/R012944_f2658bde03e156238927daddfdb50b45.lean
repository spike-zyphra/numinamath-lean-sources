import Mathlib

theorem number_theory_83755 :
    ∃ N : ℕ, 0 < N ∧ ∀ a > N, ∃ k l, k ≤ l ∧ 2011 ∣ (a / 10 ^ k) % 10 ^ (l - k + 1) := by
  use 2011
  constructor
  · -- Show that 0 < 2011
    norm_num
  · -- For all a > 2011, show existence of k, l
    intro a ha
    use a
    use a
    constructor
    · -- Show k ≤ l
      all_goals omega
    · -- Show divisibility
      have h1 : (a / 10 ^ a) % 10 ^ (a - a + 1) = 0 := by
        have h2 : a ≥ 1 := by omega
        have h3 : 10 ^ a > a := by 
          have h4 : ∀ (n : ℕ), n ≥ 1 → 10 ^ n > n := by 
            intro n hn
            induction n with 
            | zero => linarith
            | succ n ih =>
              cases n with 
              | zero => 
                omega
              | succ n => 
                simp [pow_add, pow_mul] at ih ⊢
                all_goals omega
          specialize h4 a (by omega)
          linarith
        have h4 : a / 10 ^ a = 0 := by 
          have h5 : a < 10 ^ a := h3
          have h6 : a / 10 ^ a = 0 := by 
            rw [Nat.div_eq_zero_iff]
            omega
          exact h6 
        have h6 : (a / 10 ^ a) % 10 ^ (a - a + 1) = 0 := by 
          rw [show a / 10 ^ a = 0 by exact h4]
          simp 
          all_goals omega 
        exact h6 
      rw [h1]
      all_goals norm_num