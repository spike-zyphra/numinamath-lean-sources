import Mathlib

theorem algebra_231324 {f : Polynomial ℤ} (hf : f.eval (-2) = -56) (hf' : f.eval 1 = -2)
    (hf'' : f.eval 3 = 53) (hf''' : f.eval 6 = 528) :
    f.eval 3 ≠ 53 := by

  have h1 : (3 - -2 : ℤ) ∣ (f.eval 3 - f.eval (-2)) := by 
    apply Polynomial.sub_dvd_eval_sub

  rw [hf, hf''] at h1
  norm_num at h1
  all_goals omega