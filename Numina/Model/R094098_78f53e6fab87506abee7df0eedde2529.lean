import Mathlib

theorem algebra_163001 {A B : ℕ} (hA : A ∈ Finset.Icc 0 9) (hB : B ∈ Finset.Icc 0 9)
    (h : (1001 * A + 110 * B) ^ 2 = 57108249) : 10 * A + B = 75 := by
  have hA' : 0 ≤ A := by
    simp [Finset.mem_Icc] at hA
    omega
  have hA'' : A ≤ 9 := by
    simp [Finset.mem_Icc] at hA
    omega
  have hB' : 0 ≤ B := by
    simp [Finset.mem_Icc] at hB
    omega
  have hB'' : B ≤ 9 := by
    simp [Finset.mem_Icc] at hB
    omega
  have h1 : 1001 * A + 110 * B = 7557 := by
    nlinarith
  interval_cases A <;> omega