import Mathlib

theorem algebra_7598 {a b c : ℝ} {f : ℝ → ℝ} 
    (hf : ∀x, f x = a * x^2 + b * x + c) (ha : a ≠ 0) 
    (h1 : f 13 = 0) (h2 : f 3 = 0) (h3 : f 10 = 1.4) :
    f = fun x ↦ (-1/15) * x^2 + (16/15) * x + (-13/5) := by

  have eq1 : a * 13 ^ 2 + b * 13 + c = 0 := by
    rw [hf 13] at h1
    linarith
  have eq2 : a * 3 ^ 2 + b * 3 + c = 0 := by
    rw [hf 3] at h2
    linarith
  have eq3 : a * 10 ^ 2 + b * 10 + c = 1.4 := by
    rw [hf 10] at h3
    linarith
  
  have ha' : a = -1 / 15 := by
    norm_num at eq3
    ring_nf at eq1 eq2 eq3
    linarith
  
  have hb : b = 16 / 15 := by
    norm_num at eq3
    ring_nf at eq1 eq2 eq3
    linarith [ha']
  
  have hc : c = -13 / 5 := by
    norm_num at eq3
    ring_nf at eq1 eq2 eq3
    rw [ha', hb] at eq2
    linarith
  
  funext x
  rw [hf x]
  simp [ha', hb, hc]
  <;> ring