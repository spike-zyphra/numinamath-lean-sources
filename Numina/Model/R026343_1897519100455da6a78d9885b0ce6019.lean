import Mathlib

theorem number_theory_180248 (n : ℕ) (hn : n > 0) (a : ℕ → ℝ)
    (ha : ∀ i, i + 6 < n → ∑ j ∈ Finset.range 7, a (i + j) < 0)
    (hb : ∀ i, i + 10 < n → ∑ j ∈ Finset.range 11, a (i + j) > 0) :
    n ≤ 16 := by
  by_contra h
  push_neg at h
  have h1 : n ≥ 17 := by
    omega
  have h2 := ha 0 (by
    have : (0 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h3 := ha 1 (by
    have : (1 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h4 := ha 2 (by
    have : (2 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h5 := ha 3 (by
    have : (3 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h6 := ha 4 (by
    have : (4 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h7 := ha 5 (by
    have : (5 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h8 := ha 6 (by
    have : (6 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h9 := ha 7 (by
    have : (7 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h10 := ha 8 (by
    have : (8 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h11 := ha 9 (by
    have : (9 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h12 := ha 10 (by
    have : (10 : ℕ) + 6 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h13 := hb 0 (by
    have : (0 : ℕ) + 10 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h14 := hb 1 (by
    have : (1 : ℕ) + 10 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h15 := hb 2 (by
    have : (2 : ℕ) + 10 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h16 := hb 3 (by
    have : (3 : ℕ) + 10 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h17 := hb 4 (by
    have : (4 : ℕ) + 10 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h18 := hb 5 (by
    have : (5 : ℕ) + 10 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  have h19 := hb 6 (by
    have : (6 : ℕ) + 10 < n := by
      have hn' : n ≥ 17 := by
        omega
      omega
    exact this
  )
  norm_num [Finset.sum_range_succ] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
  linarith