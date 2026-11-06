import Mathlib

theorem number_theory_324818 (x y z : ℕ) (hx : x ∈ Finset.Icc 1 9) (hy : y ∈ Finset.Icc 0 9) (hz : z ∈ Finset.Icc 0 9)
    (h : 100 * x + 10 * y + z = Nat.factorial x + Nat.factorial y + Nat.factorial z) :
    x + y + z = 10 := by
  have hx1 : x ≥ 1 := by
    simp [Finset.mem_Icc] at hx
    omega
  have hx2 : x ≤ 9 := by
    simp [Finset.mem_Icc] at hx
    omega
  have hy1 : y ≥ 0 := by
    simp [Finset.mem_Icc] at hy
    omega
  have hy2 : y ≤ 9 := by
    simp [Finset.mem_Icc] at hy
    omega
  have hz1 : z ≥ 0 := by
    simp [Finset.mem_Icc] at hz
    omega
  have hz2 : z ≤ 9 := by
    simp [Finset.mem_Icc] at hz
    omega
  interval_cases x <;> interval_cases y <;> interval_cases z <;> try simp [Nat.factorial] at h <;> try { omega }