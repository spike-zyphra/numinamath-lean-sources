import Mathlib

theorem other_274751 {p : ℝ} (hp : p ∈ Set.Icc 0 1) (h : 60 / (80 / 100 * (1 - p)) = 20 / (15 / 100 * p)) :
    p = 0.64 := by
  have h1 : 0 ≤ p := hp.1
  have h2 : p ≤ 1 := hp.2

  have h3 : p ≠ 0 := by
    by_contra h4
    rw [h4] at h
    norm_num at h
  
  have h4 : 1 - p ≠ 0 := by
    by_contra h5 
    have h5' : p = 1 := by nlinarith
    rw [h5'] at h
    norm_num at h
  
  have eq1 : 60 * (15 / 100 * p) = 20 * (80 / 100 * (1 - p)) := by
    field_simp [h3, h4] at h ⊢
    linarith
  
  have eq2 : p = (16 : ℝ) / 25 := by
    nlinarith
  
  have eq3 : p = (0.64 : ℝ) := by
    rw [eq2]
    norm_num
  
  linarith