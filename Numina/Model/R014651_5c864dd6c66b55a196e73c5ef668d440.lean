import Mathlib

theorem number_theory_218022 (m n : ℕ) :
    Nat.factorial m + 12 = n ^ 2 ↔ m = 4 ∧ n = 6 := by
  constructor
  · -- Forward direction: if $m! + 12 = n^2$, then $(m, n) = (4, 6)$.
    intro h
    by_cases h1 : m < 5
    · interval_cases m <;> try { 
      simp [Nat.factorial] at *
      all_goals
        have : n ≤ 11 := by nlinarith 
        interval_cases n <;> omega 
      }
    · -- m ≥ 5
      have h2 : m ≥ 5 := by omega 
      have h3 : 5 ∣ Nat.factorial m := by 
        apply Nat.dvd_factorial
        all_goals omega 
      have h4 : n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by
        have h5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
          omega 
        rcases h5 with (h5 | h5 | h5 | h5 | h5) <;> 
          norm_num [pow_two, Nat.mul_mod, h5] 
      have h5 : (Nat.factorial m + 12) % 5 = n ^ 2 % 5 := by 
        omega
      have h6 : (Nat.factorial m + 12) % 5 = 2 := by
        have h7 : Nat.factorial m % 5 = 0 := by
          have h8 : 5 ∣ Nat.factorial m := h3
          omega
        omega 
      omega 
  · -- Backward direction: if (m, n) = (4, 6), then $m! + 12 = n^2$.
    rintro ⟨rfl, rfl⟩ 
    norm_num [Nat.factorial]