import Mathlib

theorem number_theory_189977 (a b : ℤ) :
    Int.gcd (5*a+3*b) (13*a+8*b) = Int.gcd a b := by 
  have h1 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (Int.gcd a b : ℤ) := by
    have h2 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (5*a+3*b : ℤ) := by 
      exact Int.gcd_dvd_left
    have h3 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (13*a+8*b : ℤ) := by 
      exact Int.gcd_dvd_right
    have h4 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (a : ℤ) := by
      have h5 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (8 * (5*a+3*b) : ℤ) := by 
        apply Dvd.dvd.mul_left
        exact h2
      have h6 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (3 * (13*a+8*b) : ℤ) := by 
        apply Dvd.dvd.mul_left
        exact h3
      have h7 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (8 * (5*a+3*b) - 3 * (13*a+8*b) : ℤ) := by
        apply Dvd.dvd.sub
        · exact h5
        · exact h6
      have h8 : (8 * (5*a+3*b) - 3 * (13*a+8*b) : ℤ) = (a : ℤ) := by
        ring
      rw [h8] at h7
      exact h7
    have h5 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (b : ℤ) := by
      have h6 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (5 * (13*a+8*b) : ℤ) := by
        apply Dvd.dvd.mul_left
        exact h3
      have h7 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (13 * (5*a+3*b) : ℤ) := by
        apply Dvd.dvd.mul_left
        exact h2
      have h8 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (5 * (13*a+8*b) - 13 * (5*a+3*b) : ℤ) := by
        apply Dvd.dvd.sub
        · exact h6
        · exact h7
      have h9 : (5 * (13*a+8*b) - 13 * (5*a+3*b) : ℤ) = (b : ℤ) := by
        ring
      rw [h9] at h8
      exact h8
    have h6 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (Int.gcd a b : ℤ) := by
      apply Int.dvd_gcd
      · exact h4
      · exact h5
    exact h6
  have h2 : (Int.gcd a b : ℤ) ∣ (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) := by
    have h7 : (Int.gcd a b : ℤ) ∣ (a : ℤ) := by 
      exact Int.gcd_dvd_left
    have h8 : (Int.gcd a b : ℤ) ∣ (b : ℤ) := by 
      exact Int.gcd_dvd_right
    have h9 : (Int.gcd a b : ℤ) ∣ (5*a+3*b) := by
      apply Dvd.dvd.add
      · -- Show division of 5a
        apply Dvd.dvd.mul_left
        exact h7
      · -- Show division of 3b
        apply Dvd.dvd.mul_left
        exact h8
    have h10 : (Int.gcd a b : ℤ) ∣ (13*a+8*b : ℤ) := by
      apply Dvd.dvd.add
      · -- Show division of 13a
        apply Dvd.dvd.mul_left
        exact h7
      · -- Show division of 8b
        apply Dvd.dvd.mul_left
        exact h8
    have h6 : (Int.gcd a b : ℤ) ∣ (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) := by
      apply Int.dvd_gcd
      · exact h9
      · exact h10
    exact h6
  have h3 : Int.gcd (5*a+3*b) (13*a+8*b) = Int.gcd a b := by
    have h4 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) ∣ (Int.gcd a b : ℤ) := h1
    have h5 : (Int.gcd a b : ℤ) ∣ (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) := h2
    have h6 : (Int.gcd (5*a+3*b) (13*a+8*b) : ℤ) = (Int.gcd a b : ℤ) := by
      apply Int.dvd_antisymm 
      all_goals
        try tauto
        all_goals
          try native_decide
          all_goals
            try try tauto
      all_goals
        try try nlinarith
    exact_mod_cast h6
  exact_mod_cast h3
  <;> try try tauto
  <;> try try native_decide