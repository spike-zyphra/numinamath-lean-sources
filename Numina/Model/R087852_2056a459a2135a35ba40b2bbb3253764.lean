import Mathlib

theorem algebra_163730 {x y : ℕ} (hx : x ∈ Finset.Icc 1 6) (hy : y ∈ Finset.Icc 1 6) :
    (2 * x + 5) * 5 + y - 25 = 10 * x + y := by 
  simp [Finset.mem_Icc] at hx hy
  omega