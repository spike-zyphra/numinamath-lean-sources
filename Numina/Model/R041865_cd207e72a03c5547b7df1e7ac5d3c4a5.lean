import Mathlib

theorem number_theory_173281 (f : ℤ → ℤ) (hf0 : f 0 = 0)
    (h : ∀ k ≥ 0, ∀ n, |f ((n + 1) * 2 ^ k) - f (n * 2 ^ k)| ≤ 1) :
    f 2019 ≤ 4 := by
  have h1 := h 0 (by norm_num) 2018
  have h2 := h 1 (by norm_num) 1009
  have h3 := h 1 (by norm_num) 1008
  have h4 := h 2 (by norm_num) 504
  have h5 := h 3 (by norm_num) 252
  have h6 := h 4 (by norm_num) 126
  have h7 := h 5 (by norm_num) 63
  have h8 := h 9 (by norm_num) 1
  have h9 := h 10 (by norm_num) 0
  have h10 := h 10 (by norm_num) 1
  have h11 := h 11 (by norm_num) 0
  norm_num [abs_le] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hf0
  omega