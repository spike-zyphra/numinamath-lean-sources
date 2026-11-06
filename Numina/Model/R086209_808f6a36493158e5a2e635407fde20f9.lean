import Mathlib

theorem algebra_269269 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / (a + b) = 2) (h2 : 1 / (b + c) = 4) (h3 : 1 / (c + a) = 2.4) :
    1 / a = 3 := by 
  have eq1 : a + b ≠ 0 := by
    by_contra h
    have h4 : a + b = 0 := by linarith
    rw [h4] at h1
    norm_num at h1

  have eq2 : b + c ≠ 0 := by 
    by_contra h
    have h4 : b + c = 0 := by linarith
    rw [h4] at h2
    norm_num at h2
  
  have eq3 : c + a ≠ 0 := by
    by_contra h
    have h4 : c + a = 0 := by linarith
    rw [h4] at h3
    norm_num at h3

  have eq4 : a + b = 1 / 2 := by 
    have h5 : 1 / (a + b) = 2 := h1
    field_simp [eq1] at h5 ⊢
    linarith
  
  have eq5 : b + c = 1 / 4 := by 
    have h6 : 1 / (b + c) = 4 := h2
    field_simp [eq2] at h6 ⊢
    linarith
  
  have eq6 : c + a = 5 / 12 := by 
    have h7 : 1 / (c + a) = 2.4 := h3
    field_simp [eq3] at h7 ⊢
    ring_nf at h7 ⊢
    linarith
  
  have h_a : a = 1 / 3 := by
    linarith

  have h4 : 1 / a = 3 := by
    rw [h_a]
    norm_num
  
  exact h4