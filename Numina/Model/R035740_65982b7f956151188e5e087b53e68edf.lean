import Mathlib

theorem algebra_601178 {P : Polynomial ℤ} (hP0 : Odd (P.eval 0)) (hP1 : Odd (P.eval 1)) :
    ¬∃ x : ℤ, P.eval x = 0 := by
  by_contra h
  rcases h with ⟨x, hx⟩
  have h1 : (P.eval x) % 2 = 0 := by 
    omega
  have h2 : (P.eval x) % 2 = 1 := by
    have h1 : (P.eval 0) % 2 = 1 := by
      obtain ⟨k, hk⟩ := hP0
      omega
    have h3 : (P.eval 1) % 2 = 1 := by
      obtain ⟨k, hk⟩ := hP1
      omega
    have h4 : (P.eval x) % 2 = 1 := by
      have h5 : (x : ℤ) % 2 = 0 ∨ (x : ℤ) % 2 = 1 := by
        omega
      rcases h5 with (h5 | h5)
      · 
        have h6 : (P.eval x) % 2 = (P.eval 0) % 2 := by
          have h7 : (x : ℤ) % 2 = 0 := h5
          have h9 : (P.eval x - P.eval 0) % 2 = 0 := by
            have h10 : (x : ℤ) % 2 = 0 := h7
            have h11 : (x - (0 : ℤ)) % 2 = 0 := by
              omega
            have h14 : (x - (0 : ℤ)) ∣ (P.eval x - P.eval 0) := by
              apply Polynomial.sub_dvd_eval_sub
            have h15 : (P.eval x - P.eval 0) % 2 = 0 := by 
              exact Int.emod_eq_zero_of_dvd (show (2 : ℤ) ∣ (P.eval x - P.eval 0) by 
                have h16 : (2 : ℤ) ∣ (x - (0 : ℤ)) := by
                  omega
                have h17 : (x - (0 : ℤ)) ∣ (P.eval x - P.eval 0) := h14
                exact dvd_trans h16 h17
              )
            exact h15
          omega
        omega
      · 
        have h7 : (x : ℤ) % 2 = 1 := h5
        have h12 : (P.eval x) % 2 = (P.eval 1) % 2 := by
          have h7 : (x : ℤ) % 2 = 1 := h7
          have h9 : (P.eval x - P.eval 1) % 2 = 0 := by
            have h7 : (x : ℤ) % 2 = 1 := h7
            have h11 : (x - (1 : ℤ)) % 2 = 0 := by
              omega
            have h14 : (x - (1 : ℤ)) ∣ (P.eval x - P.eval 1) := by
              apply Polynomial.sub_dvd_eval_sub
            have h15 : (P.eval x - P.eval 1) % 2 = 0 := by 
              exact Int.emod_eq_zero_of_dvd (show (2 : ℤ) ∣ (P.eval x - P.eval 1) by 
                have h16 : (2 : ℤ) ∣ (x - (1 : ℤ)) := by
                  omega
                have h17 : (x - (1 : ℤ)) ∣ (P.eval x - P.eval 1) := h14
                exact dvd_trans h16 h17
              )
            exact h15
          omega
        omega
    exact h4
  omega