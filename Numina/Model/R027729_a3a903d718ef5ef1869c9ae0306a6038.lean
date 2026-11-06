import Mathlib

theorem number_theory_209050 (n : ℤ) :
    ¬∃ m, m = n ∧ ∀ i ∈ Finset.range 1000, ¬∃ j, j = m + i ∧ ∃ k, k = m - i := by 
  rintro ⟨m, hm, h⟩ 
  have h0 := h 0 (by simp) 
  have : ∃ j, j = m + 0 ∧ ∃ k, k = m - 0 := by 
    refine ⟨m, by simp, ⟨m - 0, by simp⟩⟩ 
  contradiction