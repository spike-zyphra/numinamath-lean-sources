import Mathlib

theorem number_theory_186470 : ¬∃ P : Polynomial ℤ, P.eval 6 = 5 ∧ P.eval 14 = 9 := by 
  rintro ⟨P, ⟨h6, h14⟩⟩
  have h : (14 - 6 : ℤ) ∣ (P.eval 14 - P.eval 6) := by
    apply Polynomial.sub_dvd_eval_sub
  rw [h6, h14] at h
  norm_num at h