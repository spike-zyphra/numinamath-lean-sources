import Mathlib

theorem number_theory_56568 {n : ℕ} (hn : n > 0) (a : ℕ → ℕ)
    (ha : ∀ i ∈ Finset.range n, a i ∈ Finset.Icc 1 n)
    (h : ∃ d, ∀ i ∈ Finset.range n, a (i + 1) = a i + d)
    (h1 : a 0 = 11) (h2 : a 1 = 4) (h3 : a 2 = 17) :
    n = 20 := by
  rcases h with ⟨d, hd⟩
  -- Apply hd for i = 0. 0 ∈ Finset.range n since 0 < n
  have h01 : a 1 = a 0 + d := by
    specialize hd 0 (by
      simp [Finset.mem_range, hn]
    )
    simpa using hd
  rw [h1] at h01
  rw [h2] at h01
  all_goals
    omega