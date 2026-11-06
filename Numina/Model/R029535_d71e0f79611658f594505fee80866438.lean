import Mathlib

theorem algebra_309215 (a b : ℝ) (f : ℝ → ℝ) (hf : f = fun x => x^2 + a * x + b) :
    max (max (|f 1|) (|f 2|)) (|f 3|) ≥ 1 / 2 := by
  have h1 : f 1 = 1 ^ 2 + a * 1 + b := by 
    rw [hf]
  have h2 : f 2 = 2 ^ 2 + a * 2 + b := by 
    rw [hf]
  have h3 : f 3 = 3 ^ 2 + a * 3 + b := by 
    rw [hf]
  by_contra h
  push_neg at h
  have h4 : |f 1| < 1 / 2 := by
    have h4 : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := by
      simpa using h
    have h5 : |f 1| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by 
      simp [max_le_iff]
    linarith
  have h5 : |f 2| < 1 / 2 := by 
    have h4 : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := by
      simpa using h
    have h6 : |f 2| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by 
      simp [max_le_iff]
    linarith
  have h6 : |f 3| < 1 / 2 := by 
    have h4 : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := by
      simpa using h
    have h7 : |f 3| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by 
      simp [max_le_iff]
    linarith
  have h7 : -1 / 2 < f 1 := by
    rw [h1] at *
    linarith [abs_lt.mp h4]
  have h8 : f 1 < 1 / 2 := by
    rw [h1] at *
    linarith [abs_lt.mp h4]
  have h10 : -1 / 2 < f 2 := by 
    rw [h2] at *
    linarith [abs_lt.mp h5]
  have h11 : f 2 < 1 / 2 := by 
    rw [h2] at *
    linarith [abs_lt.mp h5]
  have h12 : -1 / 2 < f 3 := by 
    rw [h3] at *
    linarith [abs_lt.mp h6]
  have h13 : f 3 < 1 / 2 := by 
    rw [h3] at *
    linarith [abs_lt.mp h6]
  simp only [h1] at h7 h8
  simp only [h2] at h10 h11
  simp only [h3] at h12 h13
  linarith