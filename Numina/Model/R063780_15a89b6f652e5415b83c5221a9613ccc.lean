import Mathlib

theorem number_theory_52793 (n : ℕ) (hn : n ∈ Finset.Icc 1 2009) :
    7 ∣ (4 * n ^ 6 + n ^ 3 + 5) ↔ False := by 
  rw [Finset.mem_Icc] at hn
  rcases hn with ⟨h1, h2⟩
  constructor
  · -- Assume 7 divides 4n^6 + n^3 + 5
    intro h
    interval_cases n <;> norm_num at h <;> omega
  · -- Assume False
    intro h
    cases h