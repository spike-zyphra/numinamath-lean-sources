import Mathlib

theorem number_theory_177102 (n : ℕ) (h : n ∈ Finset.Icc 41 46) :
    (50 - n)^2 + (n - 25) * 100 = n^2 := by 
  rw [Finset.mem_Icc] at h 
  rcases h with ⟨h1, h2⟩ 
  interval_cases n <;> norm_num