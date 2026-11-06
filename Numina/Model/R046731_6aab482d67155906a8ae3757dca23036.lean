import Mathlib

theorem inequalities_142239 (a b : ℝ) (h : {x : ℤ | 20*x+a > 0 ∧ 15*x-b ≤ 0} = {2, 3, 4}) :
    a * b ≤ -1200 := by
  have h1 : 2 ∈ {x : ℤ | 20 * x + a > 0 ∧ 15 * x - b ≤ 0} := by 
    rw [h]
    simp
  have h2 : 3 ∈ {x : ℤ | 20 * x + a > 0 ∧ 15 * x - b ≤ 0} := by 
    rw [h]
    simp
  have h3 : 4 ∈ {x : ℤ | 20 * x + a > 0 ∧ 15 * x - b ≤ 0} := by 
    rw [h]
    simp
  have not_1 : 1 ∉ {x : ℤ | 20 * x + a > 0 ∧ 15 * x - b ≤ 0} := by 
    rw [h]
    simp
  have not_5 : 5 ∉ {x : ℤ | 20 * x + a > 0 ∧ 15 * x - b ≤ 0} := by 
    rw [h]
    simp
  have not_0 : 0 ∉ {x : ℤ | 20 * x + a > 0 ∧ 15 * x - b ≤ 0} := by 
    rw [h]
    simp
  simp at h1 h2 h3 not_1 not_5 not_0
  ring_nf at h1 h2 h3 not_1 not_5 not_0

  have h4 : a ≤ -20 := by 
    by_contra h
    push_neg at h
    have h5 : (0 : ℝ) < 20 + a := by linarith
    have h6 : b < 15 := by
      apply not_1
      simpa using h5
    have h7 : 30 ≤ b := by
      linarith [h1.2]
    linarith

  have h5 : b ≥ 60 := by
    linarith [h3.2]
  
  nlinarith [sq_nonneg (a + 20), sq_nonneg (b - 60)]