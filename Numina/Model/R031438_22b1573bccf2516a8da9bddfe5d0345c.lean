import Mathlib

theorem number_theory_1646 (A : ℕ) (_ : 3 ∣ A) : 3 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 A)) := by 
  have h1 : A % 3 = 0 := by 
    omega 
  have h3 : (Nat.ofDigits 10 (List.reverse (Nat.digits 10 A)) ) % 3 = 0 := by 
    have h2 : (Nat.ofDigits 10 (List.reverse (Nat.digits 10 A)) ) % 3 = (Nat.ofDigits 10 (Nat.digits 10 A) ) % 3 := by 
      have h3 : ∀ (l : List ℕ), (Nat.ofDigits 10 l) % 3 = l.sum % 3 := by 
        intro l 
        induction l with 
        | nil => 
          simp [Nat.ofDigits]
          all_goals omega 
        | cons d l ih => 
          simp [Nat.ofDigits, List.sum] at *
          all_goals omega 
          all_goals 
            omega 
      have h4 : (Nat.ofDigits 10 (List.reverse (Nat.digits 10 A)) ) % 3 = (List.reverse (Nat.digits 10 A) ).sum % 3 := by 
        apply h3 
      have h5 : (Nat.ofDigits 10 (Nat.digits 10 A) ) % 3 = (Nat.digits 10 A).sum % 3 := by 
        apply h3 
      have h8 : (List.reverse (Nat.digits 10 A) ).sum = (Nat.digits 10 A).sum := by 
        rw [List.sum_reverse]
      rw [h4, h8] 
      all_goals omega 
      all_goals try tauto 
    have h6 : (Nat.ofDigits 10 (Nat.digits 10 A) ) % 3 = A % 3 := by 
      have h3 : ∀ (l : List ℕ), (Nat.ofDigits 10 l) % 3 = l.sum % 3 := by 
        intro l
        induction l with 
        | nil => 
          simp [Nat.ofDigits]
          all_goals omega 
        | cons d l ih => 
          simp [Nat.ofDigits, List.sum] at *
          all_goals omega 
          all_goals 
            omega 
      have h7 : (Nat.digits 10 A).sum % 3 = A % 3 := by 
        have h10 : (Nat.digits 10 A).sum % 3 = A % 3 := by 
          have h11 : (Nat.ofDigits 10 (Nat.digits 10 A)) % 3 = A % 3 := by 
            have h12 : Nat.ofDigits 10 (Nat.digits 10 A) = A := by 
              rw [Nat.ofDigits_digits]
              all_goals linarith
            rw [h12]
            <;> all_goals omega 
          have h13 : (Nat.digits 10 A).sum % 3 = (Nat.ofDigits 10 (Nat.digits 10 A)) % 3 := by
            have h8 : ∀ (l : List ℕ), (Nat.ofDigits 10 l) % 3 = l.sum % 3 := by
              intro l
              induction l with
              | nil => 
                simp [Nat.ofDigits]
                all_goals omega 
              | cons d l ih => 
                simp [Nat.ofDigits, List.sum] at *
                all_goals omega 
                all_goals 
                  omega 
            specialize h8 (Nat.digits 10 A)
            omega
          omega 
        omega 
      have h4 : (Nat.ofDigits 10 (Nat.digits 10 A) ) % 3 = (Nat.digits 10 A).sum % 3 := by 
        apply h3 
      omega 
    omega 
  exact Nat.dvd_of_mod_eq_zero h3