import Mathlib

theorem algebra_235227 (f : ℝ → ℝ) (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (h1 : f 2014 = 2015) (h2 : f 2015 = 0) (h3 : f 2016 = 2015) :
    f = fun x => 2015 * (x - 2015) ^ 2 := by
  rcases hf with ⟨a, b, c, h_def⟩
  have eq1 : a * (2014 : ℝ) ^ 2 + b * (2014 : ℝ) + c = 2015 := by
    rw [h_def] at h1
    simpa using h1
  have eq2 : a * (2015 : ℝ) ^ 2 + b * (2015 : ℝ) + c = 0 := by
    rw [h_def] at h2 
    simpa using h2
  have eq3 : a * (2016 : ℝ) ^ 2 + b * (2016 : ℝ) + c = 2015 := by 
    rw [h_def] at h3 
    simpa using h3 
  have ha : a = 2015 := by
    ring_nf at eq1 eq2 eq3 
    nlinarith
  have hb : b = -2015 * 4030 := by 
    rw [ha] at eq1 eq2 eq3 
    nlinarith
  have hc : c = 2015 ^ 3 := by 
    rw [ha, hb] at eq2 
    nlinarith 
  ext x 
  simp [h_def, ha, hb, hc]
  all_goals 
    ring_nf