import Mathlib


theorem algebra_10513 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (h : (x + y) / 2 = 10 * x + y) : x = 49 := by 
  simp_all [Finset.mem_Icc]
  omega