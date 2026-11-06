import Mathlib

theorem number_theory_144314 (n : ℕ) (hn : 0 < n) (a : ℕ → ℕ)
    (ha : ∀ i ∈ Finset.Icc 1 n, a i = 0) (h : ∀ m ∈ Finset.Icc 1 n, ∀ i ∈ Finset.Icc 1 n,
    m ∣ i → a i = 1 - a i) :
    ∀ i ∈ Finset.Icc 1 n, a i = 1 ↔ ∃ k, i = k^2 := by
  have h1' : a 1 = 0 := by
    specialize ha 1 (by
      simp
      all_goals omega
    )
    simpa using ha
  have h1 : a 1 = 1 - a 1 := by
    specialize h 1 (by
      simp
      all_goals omega
    ) 1 (by
      simp
      all_goals omega
    ) (by
      norm_num
    )
    simpa using h
  rw [h1'] at h1
  all_goals omega