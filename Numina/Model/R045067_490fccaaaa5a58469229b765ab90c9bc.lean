import Mathlib

theorem number_theory_610974 :
    IsGreatest {x : ℕ | ∀ n > 0, x ∣ (2002 ^ n + 2)} 6 := by
  constructor
  · -- Show 6 is in the set
    show ∀ n > 0, 6 ∣ (2002 ^ n + 2)
    intro n hn
    have h1 : ∀ n : ℕ, n > 0 → 6 ∣ (2002 ^ n + 2) := by
      intro n hn
      induction n with
      | zero =>
        linarith -- zero is not greater than 0
      | succ n ih =>
        cases n with
        | zero =>
          norm_num 
        | succ n =>
          simp [Nat.pow_succ, Nat.pow_zero] at ih ⊢
          all_goals omega
    specialize h1 n hn
    simpa using h1 
  · -- Show that 6 is greatest in the set
    intro x hx
    have h2 := hx 1 (by norm_num)
    have h3 := hx 2 (by norm_num)
    have h5 : x ∣ 6 := by
      have h2' : x ∣ 2002 + 2 := by 
        simpa using h2
      have h3' : x ∣ 2002 ^ 2 + 2 := by 
        simpa using h3
      have h4 : x ∣ Nat.gcd (2002 + 2) (2002 ^ 2 + 2) := by 
        exact Nat.dvd_gcd h2' h3'
      have h6 : Nat.gcd (2002 + 2) (2002 ^ 2 + 2) = 6 := by
        norm_num [Nat.gcd]
      rw [h6] at h4 
      exact h4 
    have h7 : x ≤ 6 := by
      exact Nat.le_of_dvd (by norm_num) h5 
    linarith