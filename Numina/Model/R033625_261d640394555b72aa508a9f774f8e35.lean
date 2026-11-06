import Mathlib

theorem number_theory_79507 {P : Polynomial ℤ} (hP5 : 2 ∣ P.eval 5) (hP2 : 5 ∣ P.eval 2) :
    10 ∣ P.eval 7 := by
  have h5_ : P.eval 7 % 2 = 0 := by
    have h6_ : P.eval 5 % 2 = 0 := by 
      omega 
    have h7_ : (P.eval 7 - P.eval 5) % 2 = 0 := by 
      have h8_ : (7 - 5 : ℤ) ∣ (P.eval 7 - P.eval 5) := by 
        apply Polynomial.sub_dvd_eval_sub 
      have h9_ : 2 ∣ (P.eval 7 - P.eval 5) := by
        have h10_ : (7 - 5 : ℤ) ∣ (P.eval 7 - P.eval 5) := h8_
        have h11_ : (7 - 5 : ℤ) = 2 := by norm_num 
        rw [h11_] at h10_ 
        exact h10_ 
      omega 
    omega 
  -- We need to prove $P(7)$ is divisible by 5.
  have h6_ : P.eval 7 % 5 = 0 := by
  -- Since $5$ divides $P(2)$, we have $P(2) \equiv 0 \pmod{5}$.
    have h7_ : P.eval 2 % 5 = 0 := by 
      omega 
    -- Because $7 \equiv 2 \pmod 5$, we have $P(7) \equiv P(2) \equiv 0 \pmod 5$.
    have h8_ : (7 - 2 : ℤ) ∣ (P.eval 7 - P.eval 2) := by
      apply Polynomial.sub_dvd_eval_sub 
    have h9_ : 5 ∣ (P.eval 7 - P.eval 2) := by
      have h10_ : (7 - 2 : ℤ) ∣ (P.eval 7 - P.eval 2) := h8_
      have h11_ : (7 - 2 : ℤ) = 5 := by norm_num 
      rw [h11_] at h10_ 
      exact h10_ 
    have h11_ : (P.eval 2) % 5 = 0 := h7_ 
    have h7_ : (P.eval 7 - P.eval 2) % 5 = 0 := by 
      exact Int.emod_eq_zero_of_dvd h9_ 
    omega 
  omega