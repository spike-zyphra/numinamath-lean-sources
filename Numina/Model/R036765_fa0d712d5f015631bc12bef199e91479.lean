import Mathlib

theorem number_theory_276813 {n : ℕ} (hn : n % 4 = 2 ∧ n % 6 = 4 ∧ n % 8 = 6) :
    n ∈ Finset.Icc 120 150 ↔ n = 142 := by
  rcases hn with ⟨h1, h2, h3⟩
  constructor
  · -- Assume n ∈ Finset.Icc 120 150, prove n = 142
    intro h
    rw [Finset.mem_Icc] at h
    rcases h with ⟨h4, h5⟩
    omega
  · -- Assume n = 142, prove n ∈ Finset.Icc 120 150
    intro h
    rw [h]
    all_goals norm_num