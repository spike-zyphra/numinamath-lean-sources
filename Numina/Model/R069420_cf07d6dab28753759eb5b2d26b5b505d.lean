import Mathlib

theorem number_theory_48647 (f : Polynomial ℤ) (hf : f.eval 2008 = 0 ∧ f.eval 2010 = 1867) :
    False := by 
  rcases hf with ⟨h1, h2⟩
  have h3 : (2010 - 2008 : ℤ) ∣ (f.eval 2010 - f.eval 2008) := by 
    apply Polynomial.sub_dvd_eval_sub
  rw [h1, h2] at h3
  norm_num at h3