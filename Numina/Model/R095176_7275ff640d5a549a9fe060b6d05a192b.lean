import Mathlib

theorem number_theory_236957 (z p : ℕ) (hz : z ∈ Finset.Icc 100 999) (hp : p = 99 - 2 * (2 * 10 + 1))
    (h : z % 10 = 1 ∧ z / 10 = 3 * (z % 10) ∧ z / 100 = 3 * (z % 10)) :
    (z + p) - (z - p) = 216 := by 
  simp [Finset.mem_Icc] at hz
  rcases h with ⟨hu, ht, hh⟩
  omega