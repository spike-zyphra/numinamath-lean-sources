import Mathlib

open Set

lemma lemma_1 :
    ∃ P : Polynomial ℤ, P.eval (-10) = 145 ∧ P.eval 9 = 164 ∧ P.eval 0 = -25 := by
  use (Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 + Polynomial.C (3 : ℤ) * Polynomial.X + Polynomial.C (-25 : ℤ))
  constructor
  · 
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · 
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · 
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]

theorem algebra_176700 :
    IsLeast {n | ∃ P : Polynomial ℤ, P.eval (-10) = 145 ∧ P.eval 9 = 164 ∧ n = |P.eval 0|} 25 := by 
  constructor 
  · -- Show 25 is in the set
    use (Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 + Polynomial.C (3 : ℤ) * Polynomial.X + Polynomial.C (-25 : ℤ))
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · -- Show 25 is the least
    intro n hn
    rcases hn with ⟨P, h1, h2, hn⟩
    have h5 : (0 - -10 : ℤ) ∣ (P.eval 0 - P.eval (-10)) := by
      apply P.sub_dvd_eval_sub 
    have h6 : (0 - 9 : ℤ) ∣ (P.eval 0 - P.eval 9) := by
      apply P.sub_dvd_eval_sub
    norm_num [h1] at h5 
    norm_num [h2] at h6 
    have h7 : P.eval 0 % 10 = 5 := by 
      omega 
    have h8 : P.eval 0 % 9 = 2 := by 
      omega 
    have h9 : |P.eval 0| ≥ 25 := by 
      have h70 : P.eval 0 % 10 = 5 := h7 
      have h71 : P.eval 0 % 9 = 2 := h8 
      by_contra h
      push_neg at h 
      have h60 : P.eval 0 > -25 := by 
        linarith [abs_lt.mp h]
      have h61 : P.eval 0 < 25 := by 
        linarith [abs_lt.mp h]
      interval_cases h90 : P.eval 0 <;> omega 
    linarith [h9, hn]