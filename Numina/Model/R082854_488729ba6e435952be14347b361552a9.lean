import Mathlib

theorem algebra_228882 (a : ℕ → ℝ) (h₀ : a 1 = 2) (h₁ : a 16 = 47)
    (h₂ : ∀ n, n ∈ Finset.Icc 2 15 → a n = (a (n - 1) + a (n + 1)) / 2) :
    a 5 = 14 := by
  have eq2 := h₂ 2 (by norm_num [Finset.mem_Icc])
  have eq3 := h₂ 3 (by norm_num [Finset.mem_Icc])
  have eq4 := h₂ 4 (by norm_num [Finset.mem_Icc])
  have eq5 := h₂ 5 (by norm_num [Finset.mem_Icc])
  have eq6 := h₂ 6 (by norm_num [Finset.mem_Icc])
  have eq7 := h₂ 7 (by norm_num [Finset.mem_Icc])
  have eq8 := h₂ 8 (by norm_num [Finset.mem_Icc])
  have eq9 := h₂ 9 (by norm_num [Finset.mem_Icc])
  have eq10 := h₂ 10 (by norm_num [Finset.mem_Icc])
  have eq11 := h₂ 11 (by norm_num [Finset.mem_Icc])
  have eq12 := h₂ 12 (by norm_num [Finset.mem_Icc])
  have eq13 := h₂ 13 (by norm_num [Finset.mem_Icc])
  have eq14 := h₂ 14 (by norm_num [Finset.mem_Icc])
  have eq15 := h₂ 15 (by norm_num [Finset.mem_Icc])
  norm_num at eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11 eq12 eq13 eq14 eq15 
  linarith [h₀, h₁, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12, eq13, eq14, eq15]