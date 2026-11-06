import Mathlib

theorem number_theory_9024 {P : Polynomial ℤ} (hP0 : Odd (P.eval 0)) (hP1 : Odd (P.eval 1)) :
    ¬∃ x : ℤ, P.eval x = 0 := by 
  rintro ⟨x, hx⟩
  have h1 : (P.eval x : ℤ) % 2 = 1 := by
    have h1 : x % 2 = 0 ∨ x % 2 = 1 := by 
      omega
    rcases h1 with (h1 | h1)
    · -- x % 2 = 0
      have h3 : (P.eval x : ℤ) % 2 = (P.eval (0 : ℤ) : ℤ) % 2 := by
        have h4 : (x - (0 : ℤ)) ∣ (P.eval x - P.eval (0 : ℤ)) := by
          apply P.sub_dvd_eval_sub
        have h6 : (2 : ℤ) ∣ (P.eval x - P.eval (0 : ℤ)) := by
          have h7 : (2 : ℤ) ∣ (x - (0 : ℤ)) := by
            have h8 : x % 2 = 0 := h1
            have h9 : (2 : ℤ) ∣ (x : ℤ) := by
              omega
            have h10 : (2 : ℤ) ∣ (x - (0 : ℤ)) := by
              have h11 : (x - (0 : ℤ) : ℤ) = x := by ring
              rw [h11]
              exact h9
            exact h10
          exact dvd_trans h7 h4
        have h7 : (P.eval x - P.eval (0 : ℤ) : ℤ) % 2 = 0 := by
          have h7 : (2 : ℤ) ∣ (P.eval x - P.eval (0 : ℤ)) := h6
          omega
        omega
      have h10 : (P.eval (0 : ℤ) : ℤ) % 2 = 1 := by
        obtain ⟨k, hk⟩ := hP0
        have h14 : (P.eval (0 : ℤ) : ℤ) = 2 * k + 1 := by linarith
        omega
      omega
    · -- x % 2 = 1
      have h3 : (P.eval x : ℤ) % 2 = (P.eval (1 : ℤ) : ℤ) % 2 := by
        have h4 : ((1 : ℤ) - (x : ℤ)) ∣ (P.eval (1 : ℤ) - P.eval x) := by
          apply P.sub_dvd_eval_sub
        have h6 : (2 : ℤ) ∣ (P.eval (1 : ℤ) - P.eval x) := by
          have h7 : (2 : ℤ) ∣ ((1 : ℤ) - (x : ℤ)) := by
            have h8 : x % 2 = 1 := h1
            omega
          exact dvd_trans h7 h4
        have h7 : (P.eval (1 : ℤ) - P.eval x : ℤ) % 2 = 0 := by
          have h7 : (2 : ℤ) ∣ (P.eval (1 : ℤ) - P.eval x) := h6
          omega
        omega
      have h10 : (P.eval (1 : ℤ) : ℤ) % 2 = 1 := by
        obtain ⟨k, hk⟩ := hP1
        have h14 : (P.eval (1 : ℤ) : ℤ) = 2 * k + 1 := by linarith
        omega
      omega
  omega