import Mathlib

theorem number_theory_837 (n : ℕ) (h : n > 200) (h1 : ∀ i ∈ Finset.range 12, n + 7 = 10 * i) :
    n = 247 := by 
  have h0 := h1 0 (Finset.mem_range.mpr (by norm_num))
  omega