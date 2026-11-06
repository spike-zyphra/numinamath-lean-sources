import Mathlib

theorem number_theory_69524 (a b c : ℕ) (ha : a ∈ Finset.Icc 1 6)
    (hb : b ∈ Finset.Icc 1 6) (hc : c ∈ Finset.Icc 1 6) (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    7 ∣ a * b * c + (7 - a) * (7 - b) * (7 - c) := by
  have ha1 : a ≥ 1 := by
    simp [Finset.mem_Icc] at ha
    omega
  have ha2 : a ≤ 6 := by
    simp [Finset.mem_Icc] at ha
    omega
  have hb1 : b ≥ 1 := by
    simp [Finset.mem_Icc] at hb
    omega
  have hb2 : b ≤ 6 := by
    simp [Finset.mem_Icc] at hb
    omega
  have hc1 : c ≥ 1 := by
    simp [Finset.mem_Icc] at hc
    omega
  have hc2 : c ≤ 6 := by
    simp [Finset.mem_Icc] at hc
    omega
  interval_cases a <;> interval_cases b <;> interval_cases c
    <;> omega