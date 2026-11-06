import Mathlib

theorem number_theory_224991 (a : ℕ → ℝ) (ha : ∀ i, i + 6 < n → ∑ j ∈ Finset.range 7, a (i + j) < 0)
    (ha' : ∀ i, i + 10 < n → ∑ j ∈ Finset.range 11, a (i + j) > 0) :
    n ≤ 16 := by
  by_contra h
  push_neg at h
  have h1 : n > 16 := by linarith
  have h2 := ha 0 (by linarith)
  have h3 := ha 1 (by linarith)
  have h4 := ha 2 (by linarith)
  have h5 := ha 3 (by linarith)
  have h6 := ha 4 (by linarith)
  have h7 := ha 5 (by linarith)
  have h8 := ha 6 (by linarith)
  have h9 := ha 7 (by linarith)
  have h10 := ha 8 (by linarith)
  have h11 := ha 9 (by linarith)
  have h12 := ha 10 (by linarith)
  have h13 : ∑ j in Finset.range 11, a (0 + j) > 0 := by
    apply ha' 0 
    omega
  have h14 : ∑ j in Finset.range 11, a (1 + j) > 0 := by
    apply ha' 1 
    omega
  have h15 : ∑ j in Finset.range 11, a (2 + j) > 0 := by 
    apply ha' 2 
    omega
  have h16 : ∑ j in Finset.range 11, a (3 + j) > 0 := by 
    apply ha' 3 
    omega
  have h17 : ∑ j in Finset.range 11, a (4 + j) > 0 := by 
    apply ha' 4 
    omega
  have h18 : ∑ j in Finset.range 11, a (5 + j) > 0 := by 
    apply ha' 5 
    omega
  have h19 : ∑ j in Finset.range 11, a (6 + j) > 0 := by 
    apply ha' 6 
    omega
  norm_num [Finset.sum_range_succ] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 
  norm_num [Finset.sum_range_succ] at h13 h14 h15 h16 h17 h18 h19 
  linarith