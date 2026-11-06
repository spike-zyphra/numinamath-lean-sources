import Mathlib

theorem algebra_102740 (a b : ℝ) (f : ℝ → ℝ) (hf : f = fun x => a * x + b + 9 / x) :
    ∃ x0 ∈ Set.Icc 1 9, |f x0| ≥ 2 := by
  by_contra h
  push_neg at h
  have h1 : |f 1| < 2 := by
    apply h
    norm_num
  have h3 : |f 3| < 2 := by
    apply h
    norm_num
  have h9 : |f 9| < 2 := by
    apply h
    norm_num
  have h1' : f 1 = a * 1 + b + 9 / (1 : ℝ) := by 
    rw [hf]
  have h3' : f 3 = a * 3 + b + 9 / (3 : ℝ) := by 
    rw [hf]
  have h9' : f 9 = a * 9 + b + 9 / (9 : ℝ) := by 
    rw [hf]
  have h10 : -2 < f 1 := by 
    linarith [abs_lt.mp h1]
  have h11 : f 1 < 2 := by 
    linarith [abs_lt.mp h1]
  have h30 : -2 < f 3 := by 
    linarith [abs_lt.mp h3]
  have h31 : f 3 < 2 := by 
    linarith [abs_lt.mp h3]
  have h90 : -2 < f 9 := by 
    linarith [abs_lt.mp h9]
  have h91 : f 9 < 2 := by 
    linarith [abs_lt.mp h9]
  simp only [h1'] at h10 h11
  simp only [h3'] at h30 h31
  simp only [h9'] at h90 h91
  norm_num at h10 h11 h30 h31 h90 h91 
  linarith