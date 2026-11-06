import Mathlib

theorem algebra_278333 (v b c : ℤ) (h : v ∈ Finset.Icc 1 10) (hb : b = v + 5) (hc : c = v - 5) :
    b - c = 10 := by
  rw [hb, hc]
  linarith -- This simplifies the expression (v + 5) - (v - 5) to 10