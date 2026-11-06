import Mathlib

open Polynomial

theorem algebra_610261 :
    IsLeast {abs (eval 0 P) | (P : ℤ[X]) (_ : P.eval (-10) = 145) (_ : P.eval 9 = 164)} 25 := by
  constructor 
  · -- We will prove that 25 can be attained.
    use 2 * X ^ 2 + 3 * X - 25
    all_goals norm_num 
  · -- We will prove that 25 is the smallest value.
    intro n hn 
    rcases hn with ⟨P, hP1, hP2, hn⟩
    have h1 : (P.eval 0) % 10 = 5 := by
      have h2 : (-10 : ℤ) ∣ (P.eval (-10) - P.eval 0) := by
        apply P.sub_dvd_eval_sub
      rw [show P.eval (-10) = 145 by simpa using hP1] at h2 
      obtain ⟨k, hk⟩ := h2
      omega
    have h3 : (P.eval 0) % 9 = 2 := by 
      have h39 : (9 - (0 : ℤ) ) ∣ (P.eval 9 - P.eval 0) := by 
        apply P.sub_dvd_eval_sub
      have h4 : (9 - (0 : ℤ) ) = (9 : ℤ) := by 
        omega 
      rw [h4] at h39 
      rw [show P.eval 9 = 164 by simpa using hP2] at h39 
      obtain ⟨k, hk⟩ := h39 
      omega
    by_contra h
    push_neg at h 
    have h4 : abs (P.eval 0) < 25 := by 
      omega 
    have h5 : P.eval 0 ≥ -24 := by 
      cases' abs_cases (P.eval 0) with h1 h1 
      all_goals omega 
    have h6 : P.eval 0 ≤ 24 := by 
      cases' abs_cases (P.eval 0) with h1 h1 
      all_goals omega
    interval_cases h7 : P.eval 0 <;> omega