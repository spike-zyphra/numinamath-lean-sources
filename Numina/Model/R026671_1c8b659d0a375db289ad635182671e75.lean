import Mathlib

theorem number_theory_246609 (a : ℕ → ℕ) (ha : a 0 = 2) (ha' : a 1 = 0) (ha'' : a 2 = 1)
    (h : ∀ n, a (n + 3) = (a n + a (n + 1) + a (n + 2)) % 10) :
    ∃ n, a n = 1 ∧ a (n + 1) = 2 ∧ a (n + 2) = 2 := by 
  have ha3 : a 3 = (a 0 + a 1 + a 2) % 10 := h 0
  rw [ha, ha', ha''] at ha3
  norm_num at ha3
  have ha4 : a 4 = (a 1 + a 2 + a 3) % 10 := h 1
  rw [ha', ha'', ha3] at ha4
  norm_num at ha4
  have ha5 : a 5 = (a 2 + a 3 + a 4) % 10 := h 2
  rw [ha'', ha3, ha4] at ha5
  norm_num at ha5
  have ha6 : a 6 = (a 3 + a 4 + a 5) % 10 := h 3
  rw [ha3, ha4, ha5] at ha6
  norm_num at ha6
  have ha7 : a 7 = (a 4 + a 5 + a 6) % 10 := h 4
  rw [ha4, ha5, ha6] at ha7
  norm_num at ha7
  have ha8 : a 8 = (a 5 + a 6 + a 7) % 10 := h 5
  rw [ha5, ha6, ha7] at ha8
  norm_num at ha8
  have ha9 : a 9 = (a 6 + a 7 + a 8) % 10 := h 6
  rw [ha6, ha7, ha8] at ha9
  norm_num at ha9
  have ha10 : a 10 = (a 7 + a 8 + a 9) % 10 := h 7
  rw [ha7, ha8, ha9] at ha10
  norm_num at ha10
  have ha11 : a 11 = (a 8 + a 9 + a 10) % 10 := h 8
  rw [ha8, ha9, ha10] at ha11
  norm_num at ha11
  have ha12 : a 12 = (a 9 + a 10 + a 11) % 10 := h 9
  rw [ha9, ha10, ha11] at ha12
  norm_num at ha12
  have ha13 : a 13 = (a 10 + a 11 + a 12) % 10 := h 10
  rw [ha10, ha11, ha12] at ha13
  norm_num at ha13
  exact ⟨11, by 
    constructor 
    · -- a 11 = 1
      exact ha11 
    constructor 
    · -- a 12 = 2
      exact ha12 
    · -- a 13 = 2
      exact ha13 
  ⟩