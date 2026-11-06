import Mathlib

theorem number_theory_221577 : ¬ ∃ P : Polynomial ℤ, P.eval 7 = 11 ∧ P.eval 11 = 13 := by
  rintro ⟨P, hp7, hp11⟩
  have h1 : (11 - 7 : ℤ) ∣ (P.eval 11 - P.eval 7) := by
    apply Polynomial.sub_dvd_eval_sub
  norm_num [hp7, hp11] at h1 
  all_goals contradiction