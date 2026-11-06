import Mathlib

theorem algebra_171093 {f : Polynomial ℤ} (hf1 : f.eval (-2) = -56) (hf2 : f.eval 1 = -2)
    (hf3 : f.eval 3 = 53) (hf4 : f.eval 6 = 528) :
    f.eval 3 ≠ 53 := by
  intro h
  have h1 : (3 - 1 : ℤ) ∣ (f.eval 3 - f.eval 1) := by
    apply f.sub_dvd_eval_sub
  rw [show f.eval 3 = 53 by linarith [hf3, h], hf2] at h1
  norm_num at h1 
  all_goals omega