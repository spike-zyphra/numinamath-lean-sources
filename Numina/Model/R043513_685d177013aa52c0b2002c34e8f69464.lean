import Mathlib

theorem number_theory_71746 {x y : ℕ} (hx : x ∈ Finset.Icc 100 999) (hy : y ∈ Finset.Icc 100 999)
    (h : 1000 * x + y = 7 * (x * y)) :
    (x, y) = (143, 143) := by
  have h1 : 100 ≤ x := by
    simp [Finset.mem_Icc] at hx
    omega
  have h2 : x ≤ 999 := by
    simp [Finset.mem_Icc] at hx
    omega
  have h3 : 100 ≤ y := by
    simp [Finset.mem_Icc] at hy
    omega
  have h4 : y ≤ 999 := by
    simp [Finset.mem_Icc] at hy
    omega
  have h5 : x = 143 := by
    interval_cases x <;> try { 
      omega 
    } 
  have h6 : y = 143 := by
    rw [h5] at h 
    nlinarith [h3, h4, h]
  simp [h5, h6]