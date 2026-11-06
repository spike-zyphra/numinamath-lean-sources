import Mathlib

theorem algebra_2936 {P : Polynomial ℤ} (hP : P.eval 1 = 3 ∧ P.eval 3 = 1) :
    ∃ a, P.eval 4 = 3 * a := by 
  have h1 : (4 - (1 : ℤ)) ∣ (P.eval 4 - P.eval 1) := by 
    apply Polynomial.sub_dvd_eval_sub
  have h2 : P.eval 1 = 3 := hP.left
  have h3 : P.eval 4 - P.eval 1 = P.eval 4 - 3 := by
    rw [h2]
  rw [h3] at h1
  rcases h1 with ⟨k, hk⟩
  use 1 + k
  linarith [hk]