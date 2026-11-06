import Mathlib

theorem number_theory_282 (x y : ℕ) (hx : x ∈ Finset.Icc 100 999) (hy : y ∈ Finset.Icc 100 999)
    (h : x * 1000 + y = 3 * (x * y)) :
    x * 1000 + y = 167334 := by 
  have h1 : x ≥ 100 := by 
    simp [Finset.mem_Icc] at hx
    linarith
  have h2 : x ≤ 999 := by 
    simp [Finset.mem_Icc] at hx
    linarith
  have h3 : y ≥ 100 := by 
    simp [Finset.mem_Icc] at hy
    linarith
  have h4 : y ≤ 999 := by 
    simp [Finset.mem_Icc] at hy
    linarith
  interval_cases x <;> omega