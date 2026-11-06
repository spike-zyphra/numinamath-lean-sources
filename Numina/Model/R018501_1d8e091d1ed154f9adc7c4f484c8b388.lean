import Mathlib

theorem number_theory_186636 : IsGreatest {x | ∀ n, x ∣ (2002 ^ (n + 1) + 2)} 6 := by 
  constructor
  · -- Show 6 is in the set.
    intro n
    have h1 : (2002 ^ (n + 1) + 2) % 6 = 0 := by
      have h2 : ∀ (n : ℕ), (2002 ^ (n + 1) + 2) % 6 = 0 := by 
        intro n 
        induction n with
        | zero =>
          norm_num 
        | succ n ih =>
          have eq3 : (2002 ^ (n + 2) + 2) % 6 = 0 := by
            simp [Nat.pow_succ, Nat.add_mod, Nat.mul_mod] at ih ⊢
            omega 
          exact eq3 
      exact h2 n 
    have h2 : 6 ∣ (2002 ^ (n + 1) + 2) := by 
      omega 
    exact h2 
  · -- Show 6 is greatest in the set.
    intro x hx 
    have h1 : ∀ n, x ∣ (2002 ^ (n + 1) + 2) := hx
    have h2 := h1 0
    have h3 := h1 1 
    have h4 : x ∣ 2004 := by 
      exact h2 
    have h5 : x ∣ 4008006 := by 
      exact h3 
    have h6 : x ∣ 6 := by 
      exact Nat.dvd_gcd h4 h5 
    have h7 : x ≤ 6 := by 
      exact Nat.le_of_dvd (by norm_num) h6 
    linarith