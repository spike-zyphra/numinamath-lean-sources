import Mathlib

theorem number_theory_149865 {n : ℕ} (hn : n > 0) (a : ℕ → ℝ)
    (hsum : ∀ i, i + 6 < n → ∑ j ∈ Finset.range 7, a (i + j) < 0)
    (hsum' : ∀ i, i + 10 < n → ∑ j ∈ Finset.range 11, a (i + j) > 0) :
    n ≤ 16 := by 
  by_contra h
  push_neg at h
  have h1 : n ≥ 17 := by
    omega
  have h2 := hsum 0 (by linarith)
  have h3 := hsum 1 (by linarith)
  have h4 := hsum 2 (by linarith)
  have h5 := hsum 3 (by linarith)
  have h6 := hsum 4 (by linarith)
  have h7 := hsum 5 (by linarith)
  have h8 := hsum 6 (by linarith)
  have h9 := hsum 7 (by linarith)
  have h10 := hsum 8 (by linarith)
  have h11 := hsum 9 (by linarith)
  have h12 := hsum 10 (by linarith)
  have h13 := hsum' 0 (by linarith)
  have h14 := hsum' 1 (by linarith)
  have h15 := hsum' 2 (by linarith)
  have h16 := hsum' 3 (by linarith)
  have h17 := hsum' 4 (by linarith)
  have h18 := hsum' 5 (by linarith)
  have h19 := hsum' 6 (by linarith)
  norm_num [Finset.sum_range_succ] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 
  linarith