import Mathlib

theorem number_theory_257636 :
  {p : ℕ | p.Prime ∧ ∀ n, ¬p ∣ n → n^2 ≡ 1 [MOD p]} = 
  {2, 3} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume p is a prime such that for all n, if ¬p ∣ n then n^2 ≡ 1 [MOD p]
    intro h
    rcases h with ⟨h_prime, h_prop⟩
    by_cases hp2 : p > 3
    · 
      -- Let's show that p divides 3 by using the property with n = 2
      have h2 : ¬p ∣ 2 := by 
        by_contra h
        have h3 : p ≤ 2 := by 
          exact Nat.le_of_dvd (by omega) h
        omega
      -- Apply the property to n = 2
      have h4 := h_prop 2 h2
      have h5 : (2 : ℕ) ^ 2 % p = 1 % p := by 
        exact h4
      have h7 : p ∣ 3 := by 
        have h9 : (2 ^ 2 : ℕ) % p = 1 % p := h5
        have h10 : p ∣ ((2 ^ 2 : ℕ) - 1) := by
          exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h9)
        have h11 : (2 ^ 2 : ℕ) - 1 = 3 := by
          norm_num
        rw [h11] at h10
        exact h10
      -- Now p divides 3 and p > 3 contradicts
      have h8 : p ≤ 3 := by 
        exact Nat.le_of_dvd (by omega) h7
      omega
    · 
      -- p <= 3
      have hp3 : p ≤ 3 := by
        omega
      have h8 : p = 2 ∨ p = 3 := by
        interval_cases p <;> try tauto
      tauto
  · -- Show that 2 and 3 satisfy the condition
    rintro (rfl | rfl)
    · 
      constructor 
      · 
        norm_num
      · 
        intro n hn
        have h13 : n % 2 = 1 := by 
          omega
        simp [Nat.ModEq, Nat.pow_mod, h13]
    · 
      constructor 
      · 
        norm_num
      · 
        intro n hn
        have h13 : n % 3 = 1 ∨ n % 3 = 2 := by 
          omega
        simp [Nat.ModEq] at *
        rcases h13 with (h13 | h13)
        · 
          simp [Nat.pow_mod, h13]
        · 
          simp [Nat.pow_mod, h13]