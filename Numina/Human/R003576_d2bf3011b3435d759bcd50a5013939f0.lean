import Mathlib

theorem number_theory_197739 (F : ℤ → ℤ)
    (hF : ∀ n, F (n + 2) = F (n + 1) + F n)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    ∑ i ∈ Finset.range 11, F (-5 + i) = 16 := by 
  have hF2 := hF 0
  have hF3 := hF 1
  have hF4 := hF 2
  have hF5 := hF 3
  have hF6 := hF 4
  have hF7 := hF 5
  have hF8 := hF (-1)
  have hF9 := hF (-2)
  have hF10 := hF (-3)
  have hF11 := hF (-4)
  have hF12 := hF (-5)
  have hF13 := hF (-6)
  simp [Finset.sum_range_succ, hF0, hF1] at *
  linarith