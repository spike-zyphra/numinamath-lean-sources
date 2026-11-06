import Mathlib

theorem number_theory_15366 (N : ℤ) (h : 7.5 < (N / 3 : ℝ) ∧ (N / 3 : ℝ) < 8) :
    N = 23 := by 
  have h1 : 7.5 < (N / 3 : ℝ) := h.1
  have h2 : (N / 3 : ℝ) < 8 := h.2
  have h3 : (22.5 : ℝ) < (N : ℝ) := by
    -- multiplying both sides by 3
    have h_mul : (7.5 : ℝ) * 3 < (N : ℝ) := by 
      have h' : (7.5 : ℝ) < (N / 3 : ℝ) := h1
      linarith
    linarith
  have h4 : (N : ℝ) < (24 : ℝ) := by
    -- multiplying both sides by 3
    have h_mul : (N : ℝ) < (8 : ℝ) * 3 := by 
      have h' : (N / 3 : ℝ) < (8 : ℝ) := h2
      linarith
    linarith
  have h5 : N > 22 := by
    -- convert real inequality to integer, $22.5 < N$ implies $N > 22$
    by_contra h6
    push_neg at h6
    have h6' : N ≤ 22 := by omega
    have h6'' : (N : ℝ) ≤ (22 : ℝ) := by exact_mod_cast h6'
    have h6''' : (22.5 : ℝ) ≤ (22 : ℝ) := by linarith [h3, h6'']
    norm_num at h6'''
  have h7 : N < 24 := by
    -- convert real inequality to integer, $N < 24$ implies $N < 24$
    by_contra h8
    push_neg at h8
    have h8' : N ≥ 24 := by omega
    have h8'' : (N : ℝ) ≥ (24 : ℝ) := by exact_mod_cast h8'
    linarith -- with h4
  have : N = 23 := by
    omega
  exact this