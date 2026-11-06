import Mathlib

theorem number_theory_45387 :
    ¬∃ f : Polynomial ℤ, f.eval 7 = 11 ∧ f.eval 11 = 13 := by 
  rintro ⟨f, h1, h2⟩
  have h3 : (11 - 7 : ℤ) ∣ (f.eval 11 - f.eval 7) := by
    apply Polynomial.sub_dvd_eval_sub
  rw [h1, h2] at h3
  norm_num at h3