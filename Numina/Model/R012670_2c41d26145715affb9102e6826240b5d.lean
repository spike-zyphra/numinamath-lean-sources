import Mathlib

theorem number_theory_294699 {f : Polynomial ℤ} (hf2 : 6 ∣ f.eval 2) (hf3 : 6 ∣ f.eval 3) :
    6 ∣ f.eval 5 := by

  have h1 : (5 - 2 : ℤ) ∣ (f.eval 5 - f.eval 2) := by
    apply f.sub_dvd_eval_sub

  have h2 : (5 - 3 : ℤ) ∣ (f.eval 5 - f.eval 3) := by
    apply f.sub_dvd_eval_sub

  have h3 : (f.eval 5 - f.eval 2) % 3 = 0 := by
    have h4 : (5 - 2 : ℤ) ∣ (f.eval 5 - f.eval 2) := h1
    omega

  have h4 : (f.eval 5 - f.eval 3) % 2 = 0 := by
    have h5 : (5 - 3 : ℤ) ∣ (f.eval 5 - f.eval 3) := h2
    omega

  have h5 : f.eval 2 % 3 = 0 := by
    omega

  have h6 : f.eval 3 % 2 = 0 := by
    omega

  have h7 : f.eval 5 % 3 = 0 := by
    omega

  have h8 : f.eval 5 % 2 = 0 := by
    omega

  omega