import Mathlib

theorem number_theory_197255 {P : Polynomial ℤ} (hP : Odd (P.eval 0) ∧ Odd (P.eval 1)) :
    ¬∃ x : ℤ, P.eval x = 0 := by
  intro h
  rcases h with ⟨x, hx⟩ 
  have h1 : P.eval x % 2 = 0 := by 
    rw [hx]
    norm_num 
  have h2 : P.eval 0 % 2 = 1 := by 
    rcases hP.1 with ⟨k, hk⟩
    omega 
  have h3 : P.eval 1 % 2 = 1 := by 
    rcases hP.2 with ⟨k, hk⟩
    omega 
  by_cases h4 : x % 2 = 0 
  · -- x is even 
    have h5 : P.eval x % 2 = P.eval 0 % 2 := by 
      have h6 : (x - 0 : ℤ) ∣ (P.eval x - P.eval 0 : ℤ) := by 
        apply Polynomial.sub_dvd_eval_sub
      have h7 : (x - 0 : ℤ) ∣ (P.eval x - P.eval 0 : ℤ) := h6
      have h8 : x - (0 : ℤ) = x := by ring_nf 
      rw [h8] at h7 
      have h9 : x % 2 = 0 := h4 
      have h10 : (P.eval x - P.eval 0 : ℤ) % 2 = 0 := by 
        rcases h7 with ⟨k, hk⟩ 
        have h11 : (x : ℤ) % 2 = 0 := by 
          omega 
        have h12 : x * k = P.eval x - P.eval 0 := by 
          linarith 
        have h13 : (x * k : ℤ) % 2 = 0 := by 
          simp [Int.add_emod, Int.mul_emod, h11] 
        omega 
      omega 
    omega 
  · -- x is odd 
    have h11 : x % 2 = 1 := by 
      omega 
    have h5 : P.eval x % 2 = P.eval 1 % 2 := by 
      have h6 : (x - (1 : ℤ)) ∣ (P.eval x - P.eval 1 : ℤ) := by 
        apply Polynomial.sub_dvd_eval_sub
      have h15 : x - (1 : ℤ) ∣ (P.eval x - P.eval 1 : ℤ) := h6 
      have h10 : x % 2 = 1 := by 
        omega 
      have h11 : (x - 1 : ℤ) % 2 = 0 := by 
        have h10 : x % 2 = 1 := by 
          omega 
        omega 
      have h14 : (P.eval x - P.eval 1 : ℤ) % 2 = 0 := by 
        rcases h15 with ⟨k, hk⟩ 
        have h11 : (x - 1 : ℤ) % 2 = 0 := by 
          omega 
        have h12 : (x - 1) * k = P.eval x - P.eval 1 := by 
          linarith 
        have h13 : ((x - 1) * k : ℤ) % 2 = 0 := by 
          simp [Int.add_emod, Int.mul_emod, h11] 
        omega 
      omega 
    omega