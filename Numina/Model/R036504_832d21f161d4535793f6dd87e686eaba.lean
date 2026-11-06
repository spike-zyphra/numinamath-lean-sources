import Mathlib

theorem number_theory_73053 :
    IsLeast {x : ℕ | ∃ P : Polynomial ℤ, P.eval (-10) = 145 ∧ P.eval 9 = 164 ∧ x = |P.eval 0|} 25 := by
  constructor
  · -- Show 25 is in the set.
    use 2 * (Polynomial.X) ^ 2 + 3 * (Polynomial.X) - 25
    all_goals
      norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, abs]
  · -- Show there is no smaller element in the set.
    intro x hx
    rcases hx with ⟨P, h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : P.eval (-10) = 145 := h1
    have h5 : P.eval 9 = 164 := h2
    have h6 : (9 - (0 : ℤ)) ∣ (P.eval 9 - P.eval 0) := by
      apply P.sub_dvd_eval_sub
    have h7 : ( (0 : ℤ) - (-10) ) ∣ (P.eval 0 - P.eval (-10) ) := by
      apply P.sub_dvd_eval_sub
    have h8 : (9 : ℤ) ∣ (164 - P.eval 0) := by
      norm_num at h6 ⊢
      omega
    have h9 : (10 : ℤ) ∣ (P.eval 0 - 145) := by
      norm_num at h7 ⊢
      omega
    have h11 : x < 25 := by
      omega
    have h12 : |P.eval 0| < 25 := by
      linarith [h3, h11]
    have h13 : -25 < P.eval 0 := by
      cases' abs_lt.mp h12 with h14 h15
      linarith
    have h14 : P.eval 0 < 25 := by
      cases' abs_lt.mp h12 with h15 h16
      linarith
    omega