import Mathlib

theorem algebra_115262 {P : Polynomial ℤ} (hP1 : P.eval 5 % 2 = 0) (hP2 : P.eval 2 % 5 = 0) :
    P.eval 7 % 10 = 0 := by
  have h1 : (7 - 5 : ℤ) ∣ (P.eval 7 - P.eval 5) := by
    apply P.sub_dvd_eval_sub
  have h2 : (P.eval 7 - P.eval 5) % 2 = 0 := by
    have h3 : (7 - 5 : ℤ) ∣ (P.eval 7 - P.eval 5) := by
      apply P.sub_dvd_eval_sub
    have h4 : (7 - 5 : ℤ) = 2 := by norm_num
    rw [h4] at h3
    have h5 : (P.eval 7 - P.eval 5) % 2 = 0 := by
      exact Int.emod_eq_zero_of_dvd h3
    exact h5
  have h3 : P.eval 7 % 2 = 0 := by
    have h4 : (P.eval 7 - P.eval 5) % 2 = 0 := h2
    have h5 : P.eval 5 % 2 = 0 := hP1
    have h6 : P.eval 7 % 2 = 0 := by
      omega
    exact h6
  have h4 : (7 - 2 : ℤ) ∣ (P.eval 7 - P.eval 2) := by
    apply P.sub_dvd_eval_sub
  have h5 : (P.eval 7 - P.eval 2) % 5 = 0 := by
    have h6 : (7 - 2 : ℤ) ∣ (P.eval 7 - P.eval 2) := by
      apply P.sub_dvd_eval_sub
    have h7 : (7 - 2 : ℤ) = 5 := by norm_num
    rw [h7] at h6
    have h8 : (P.eval 7 - P.eval 2) % 5 = 0 := by
      exact Int.emod_eq_zero_of_dvd h6
    exact h8
  have h6 : P.eval 7 % 5 = 0 := by
    have h7 : (P.eval 7 - P.eval 2) % 5 = 0 := h5
    have h8 : P.eval 2 % 5 = 0 := hP2
    have h9 : P.eval 7 % 5 = 0 := by
      omega
    exact h9
  have h9 : P.eval 7 % 2 = 0 := h3
  have h10 : P.eval 7 % 5 = 0 := h6
  have h11 : P.eval 7 % 10 = 0 := by
    omega
  exact h11