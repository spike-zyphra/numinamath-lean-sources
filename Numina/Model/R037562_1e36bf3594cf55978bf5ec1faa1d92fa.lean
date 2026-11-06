import Mathlib

theorem algebra_149960 (a k : ℕ) (ha : a - k ≥ 0)
    (h : a + 3 = 4 * (k + 2 - (a - k))) (h' : k ∈ Finset.Icc 14 19) :
    a = 25 := by
  have h1 : k ≥ 14 := by
    simp [Finset.mem_Icc] at h'
    omega
  have h2 : k ≤ 19 := by
    simp [Finset.mem_Icc] at h'
    omega
  have h3 : a - k ≤ a := by 
    omega
  interval_cases k <;> omega