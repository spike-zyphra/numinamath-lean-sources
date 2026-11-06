import Mathlib

theorem number_theory_177946 (n : ℕ) (h : n ∈ Finset.Icc 100 999) :
    91 ∣ (n * 1000 + n) := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨hn1, hn2⟩
  have h1 : n * 1000 + n = n * 1001 := by ring
  rw [h1]
  use n * 11
  ring_nf