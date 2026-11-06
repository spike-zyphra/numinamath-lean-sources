import Mathlib

theorem number_theory_244339 :
    IsGreatest {x | ∃ n, x = (Nat.factorial n)^2 ∧ x ∣ Nat.factorial 10} ((Nat.factorial 6)^2) := by
  constructor
  · -- First, show that (Nat.factorial 6) ^ 2 is in the set.
    use 6
    all_goals 
      native_decide
  · -- Now, show that (Nat.factorial 6) ^ 2 is greatest in the set
    intro x hx
    rcases hx with ⟨n, rfl, hx⟩
    have h4 : (Nat.factorial n : Nat) ^ 2 ∣ Nat.factorial 10 := hx
    have h8 : (Nat.factorial n : Nat) ^ 2 ≤ Nat.factorial 10 := by 
      exact Nat.le_of_dvd (by positivity) h4
    by_contra h 
    push_neg at h
    have h1 : n ≥ 7 := by 
      by_contra h2
      push_neg at h2
      have h3 : n ≤ 6 := by linarith 
      interval_cases n <;> norm_num [Nat.factorial] at h ⊢ 
      <;> try { contradiction }
    have h7 : (Nat.factorial n : Nat) ^ 2 ≥ (Nat.factorial 7 : Nat) ^ 2 := by
      have h10 : n ≥ 7 := h1 
      have h11 : Nat.factorial n ≥ Nat.factorial 7 := by 
        apply Nat.factorial_le 
        all_goals linarith 
      have h12 : (Nat.factorial n : Nat) ≥ (Nat.factorial 7 : Nat) := by linarith 
      nlinarith [show (0 : Nat) < (Nat.factorial 7 : Nat) by positivity]
    have h10 : (Nat.factorial 7 : Nat) ^ 2 > Nat.factorial 10 := by 
      norm_num [Nat.factorial]
    nlinarith [h7, h10, h8]