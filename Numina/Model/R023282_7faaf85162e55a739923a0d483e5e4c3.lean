import Mathlib

theorem number_theory_156994 (n : ℕ) :
    7 ∣ n ↔ ∃ m, 7 ∣ |(2 * (n % 10) : ℤ) - m| ∧ m = n / 10 := by
  constructor
  · -- Assume 7 divides n, we need to show exists m, 7 divides |2(n%10) - m| and m = n/10
    intro h
    use n / 10
    constructor
    · -- Show 7 divides |(2*(n%10) : ℤ) - m| where m = n / 10
      have h2 : (7 : ℤ) ∣ ((2 * (n % 10) : ℤ) - (n / 10 : ℤ)) := by
        have h5 : (n : ℤ) % 7 = 0 := by omega
        have h8 : ( (10 * (n / 10) + (n % 10 ) : ℤ )) % 7 = 0 := by 
          have h23 : ( (10 * (n / 10) + (n % 10 ) : ℤ )) = (n : ℤ ) := by
            omega
          rw [h23]
          omega
        have h9 : (7 : ℤ) ∣ (2 * (n % 10) - (n / 10 : ℤ)) := by 
          omega
        exact h9
      have h7 : (7 : ℤ) ∣ |(2 * (n % 10) : ℤ) - (n / 10 : ℤ)| := by
        have h9 : (7 : ℤ) ∣ ((2 * (n % 10) - (n / 10 : ℤ) : ℤ)) := h2
        have h6 : ((2 * (n % 10) - (n / 10 : ℤ) ) : ℤ ) % 7 = 0 := by 
          omega
        have h8' : |(2 * (n % 10) : ℤ) - (n / 10 : ℤ)| % 7 = 0 := by
          cases' abs_cases ((2 * (n % 10) : ℤ) - (n / 10 : ℤ)) with h1 h1 <;> omega
        exact Int.dvd_of_emod_eq_zero h8'
      exact_mod_cast h7
    · -- Show m = n / 10
      rfl
  · -- Assume ∃ m, 7 ∣ |(2 * (n % 10) : ℤ) - m| ∧ m = n / 10, prove 7 ∣ n
    rintro ⟨m, h1, hm⟩
    rw [hm] at h1
    have h10 : (7 : ℤ) ∣ ((2 * (n % 10) : ℤ) - (n / 10 : ℤ)) := by
      cases' abs_cases ((2 * (n % 10) : ℤ) - (n / 10 : ℤ)) with h2 h2 <;> try { 
        omega 
      } <;> try { 
        exfalso 
      }
    -- Need to show that 7 divides n
    have h5 : (n : ℤ) % 7 = 0 := by
      have h8 : (7 : ℤ) ∣ ((2 * (n % 10) : ℤ) - (n / 10 : ℤ)) := h10
      have h9 : (n : ℤ) % 7 = 0 := by
        have eq : (10 * (n / 10) + (n % 10) : ℤ) % 7 = 0 := by
          omega
        have h7 : (10 * (n / 10) + (n % 10) : ℤ ) % 7 = 0 := by
          omega
        omega
      omega
    have h8' : (7 : ℤ) ∣ (n : ℤ) := by 
      omega
    exact_mod_cast (show (7 : ℕ) ∣ (n : ℕ) by 
      omega
    )