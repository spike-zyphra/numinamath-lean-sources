import Mathlib

theorem algebra_20396 {x y : ℤ} (hx : x ∈ Finset.Icc 1 10) (hy : y ∈ Finset.Icc 1 10)
    (h : (x - 4) * (2 * y - 1) = x * y + 1) :
    x * y = 54 := by
  have h1 : x ≥ 1 := by 
    simp [Finset.mem_Icc] at hx 
    linarith
  have h2 : x ≤ 10 := by 
    simp [Finset.mem_Icc] at hx 
    linarith
  have h3 : y ≥ 1 := by 
    simp [Finset.mem_Icc] at hy 
    linarith
  have h4 : y ≤ 10 := by 
    simp [Finset.mem_Icc] at hy 
    linarith
  
  interval_cases x <;> interval_cases y <;> omega