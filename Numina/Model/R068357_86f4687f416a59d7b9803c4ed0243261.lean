import Mathlib

theorem algebra_317687 (a b c : ℤ) (ha : a ∈ Finset.Icc 1 9) (hb : b ∈ Finset.Icc 1 9)
    (hc : c ∈ Finset.Icc 1 9) (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (a + b + c : ℝ) / (a * b * c) ≤ 1 := by
  have ha1 : 1 ≤ a := by
    simp [Finset.mem_Icc] at ha 
    linarith
  have ha2 : a ≤ 9 := by
    simp [Finset.mem_Icc] at ha 
    linarith
  have hb1 : 1 ≤ b := by
    simp [Finset.mem_Icc] at hb
    linarith
  have hb2 : b ≤ 9 := by
    simp [Finset.mem_Icc] at hb
    linarith
  have hc1 : 1 ≤ c := by
    simp [Finset.mem_Icc] at hc
    linarith
  have hc2 : c ≤ 9 := by
    simp [Finset.mem_Icc] at hc
    linarith
  interval_cases a <;> interval_cases b <;> interval_cases c
    <;> norm_num
    <;> tauto