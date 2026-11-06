import Mathlib

theorem algebra_286615 {f : Polynomial ℤ} (hf : f.eval 2 % 6 = 0 ∧ f.eval 3 % 6 = 0) :
    f.eval 5 % 6 = 0 := by
  have h1 : f.eval 2 % 6 = 0 := hf.1
  have h2 : f.eval 3 % 6 = 0 := hf.2

  have h1' : (f.eval 5 - f.eval 2) % 3 = 0 := by
    have h52 : (5 - 2 : Int) ∣ f.eval 5 - f.eval 2 := by 
      apply f.sub_dvd_eval_sub
    omega

  have h2' : f.eval 5 % 3 = 0 := by
    omega

  have h2'2 : (f.eval 5 - f.eval 3) % 2 = 0 := by
    have h53 : (5 - 3 : Int) ∣ f.eval 5 - f.eval 3 := by
      apply f.sub_dvd_eval_sub
    omega

  have h3' : f.eval 5 % 2 = 0 := by 
    omega

  omega