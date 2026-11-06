import Mathlib

theorem algebra_225179 {n : ℕ} (hn : n ≥ 3) (a b : ℕ → ℝ)
    (hsum : ∑ i ∈ Finset.range n, a i = ∑ i ∈ Finset.range n, b i)
    (ha : 0 < a 0) (hinc : ∀ i ∈ Finset.range (n - 1), a i = a (i + 1))
    (h : ∀ i ∈ Finset.range (n - 2), a i + a (i + 1) = a (i + 2))
    (hb : 0 < b 0) (hinc' : ∀ i ∈ Finset.range (n - 1), b i ≤ b (i + 1))
    (h' : ∀ i ∈ Finset.range (n - 2), b i + b (i + 1) ≤ b (i + 2)) :
    a (n - 1) + a n ≤ b (n - 1) + b n := by

  have h1 : a 0 = a 1 := by
    have h0 : (0 : ℕ) ∈ Finset.range (n - 1) := by
      have h3 : n - 1 ≥ 1 := by 
        omega
      simp [Finset.mem_range] at *
      all_goals try { omega }
    specialize hinc 0 h0
    simpa using hinc

  have h2 : a 1 = a 2 := by
    have h0 : (1 : ℕ) ∈ Finset.range (n - 1) := by
      have h3 : n - 1 ≥ 2 := by 
        omega
      simp [Finset.mem_range] at *
      all_goals try { omega }
    specialize hinc 1 h0
    simpa using hinc

  have h3 : a 0 + a 1 = a 2 := by
    have h0 : (0 : ℕ) ∈ Finset.range (n - 2) := by
      have h3 : n - 2 ≥ 1 := by 
        omega
      simp [Finset.mem_range] at *
      all_goals try { omega }
    specialize h 0 h0
    simpa using h

  have h4 : a 2 = a 0 := by
    linarith [h1, h2]

  have h5 : a 0 = 0 := by
    rw [show a 1 = a 0 by linarith [h1] ] at h3
    rw [show a 2 = a 0 by linarith [h4] ] at h3
    linarith

  linarith