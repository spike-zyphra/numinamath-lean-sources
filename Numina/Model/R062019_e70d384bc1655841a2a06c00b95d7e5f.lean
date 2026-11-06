import Mathlib

theorem algebra_145135 (P : Polynomial ℤ) : ¬(P.eval 7 = 5 ∧ P.eval 15 = 9) := by 
  rintro ⟨h1, h2⟩
  have h3 : (15 - 7 : ℤ) ∣ (P.eval 15 - P.eval 7) := by
    apply Polynomial.sub_dvd_eval_sub
  rw [h1, h2] at h3
  norm_num at h3 <;> omega