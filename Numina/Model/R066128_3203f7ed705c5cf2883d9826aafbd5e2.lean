import Mathlib

theorem algebra_160830 {P : Polynomial ℤ} (hP : P.eval 7 = 5 ∧ P.eval 15 = 9) :
    False := by
  rcases hP with ⟨h1, h2⟩
  have h3 : (15 : ℤ) - (7 : ℤ) ∣ (P.eval 15 - P.eval 7) := by
    apply Polynomial.sub_dvd_eval_sub
  have h4 : (P.eval 15 - P.eval 7 : ℤ) = (9 - 5 : ℤ) := by
    rw [h2, h1]
  norm_num [h4] at h3
  all_goals omega