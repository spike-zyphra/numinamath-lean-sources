import Mathlib

theorem number_theory_233242 (h : 312 ≤ n ∧ n < 321) :
    n ∈ Finset.Ico 312 321 := by
  rcases h with ⟨h1, h2⟩
  exact Finset.mem_Ico.mpr ⟨h1, h2⟩