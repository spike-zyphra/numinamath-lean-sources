import Mathlib

theorem number_theory_94965 (n : ℕ) (h : n ∈ Finset.Icc 1 9) :
    IsSquare (∑ i in Finset.Icc 1 9 \ {n}, i) ↔ n = 9 := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨hn1, hn9⟩
  interval_cases n <;> native_decide