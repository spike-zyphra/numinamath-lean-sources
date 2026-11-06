import Mathlib

theorem algebra_225416 {P : Polynomial ℤ} (hP : P.eval (-4) = 5) (hP' : P.eval 5 = -4) :
    P.eval 0 % 60 ≤ 41 := by
  have h1 : (5 - (0 : ℤ)) ∣ (P.eval 5 - P.eval 0) := by 
    apply Polynomial.sub_dvd_eval_sub
  have h2 : (0 - (-4 : ℤ)) ∣ (P.eval 0 - P.eval (-4)) := by 
    apply Polynomial.sub_dvd_eval_sub
  rw [hP'] at h1
  rw [hP] at h2
  norm_num at h1 h2
  have h3 : P.eval 0 % 4 = 1 := by
    omega
  have h4 : P.eval 0 % 5 = 1 := by
    omega
  have h12 : P.eval 0 % 20 = 1 := by 
    have h3' : P.eval 0 % 4 = 1 := h3
    have h4' : P.eval 0 % 5 = 1 := h4
    have : P.eval 0 % 20 = 1 := by 
      have h13 : P.eval 0 % 4 = 1 := h3'
      have h14 : P.eval 0 % 5 = 1 := h4'
      have h15 : P.eval 0 % 20 = 1 ∨ P.eval 0 % 20 = 5 ∨ P.eval 0 % 20 = 9 ∨ P.eval 0 % 20 = 13 ∨ P.eval 0 % 20 = 17 := by
        omega
      rcases h15 with (h | h | h | h | h)
      · 
        omega
      · 
        omega
      · 
        omega
      · 
        omega
      · 
        omega
    omega
  have h9 : P.eval 0 % 60 ≤ 41 := by
    have h12 : P.eval 0 % 20 = 1 := h12
    omega
  exact h9