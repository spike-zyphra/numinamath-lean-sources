import Mathlib

theorem number_theory_304410 (m n : ℕ) (hm : 1 < m) (hn : 1 < n)
    (h : ∃ k, ∀ i ∈ Finset.range n, (i + 1) + (1 / 7 : ℚ) * (m - ∑ j ∈ Finset.range i, (j + 1)) = k) :
    k = 6 := by
  rcases h with ⟨k, hk⟩
  have eq1 := hk 0 (Finset.mem_range.mpr (by linarith))
  have eq2 := hk 1 (Finset.mem_range.mpr (by linarith))
  norm_num at eq1 eq2
  exfalso
  have hContr : (7 : ℚ) = (13 : ℚ) := by
    have eq3 : 1 + (m : ℚ) / 7 = 2 + (m : ℚ) / 7 - (1/7 : ℚ) := by
      field_simp at eq1 eq2 ⊢
      nlinarith
    field_simp at eq3 ⊢
    linarith
  linarith