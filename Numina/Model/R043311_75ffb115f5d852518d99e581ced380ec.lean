import Mathlib

theorem algebra_225188 : ¬∃ P : Polynomial ℤ, P.eval 7 = 11 ∧ P.eval 11 = 13 := by
  rintro ⟨P, h₁, h₂⟩
  have h3 : (11 - 7 : ℤ) ∣ (P.eval 11 - P.eval 7) := by
    apply P.sub_dvd_eval_sub
  rw [show (P.eval 11 - P.eval 7 : ℤ) = 2 by omega] at h3
  norm_num at h3
  all_goals omega