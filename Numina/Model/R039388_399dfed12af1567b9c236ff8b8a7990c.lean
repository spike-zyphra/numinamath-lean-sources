import Mathlib

theorem algebra_271825 (p q r s : ℕ) (h₀ : p ≠ 0) (h₁ : q ≠ 0) (h₂ : r ≠ 0)
    (h₃ : s ≠ 0) (h₄ : p ≠ q) (h₅ : p ≠ r) (h₆ : p ≠ s) (h₇ : q ≠ r) (h₈ : q ≠ s)
    (h₉ : r ≠ s) (h₁₀ : p ∈ Finset.Icc 1 4) (h₁₁ : q ∈ Finset.Icc 1 4) (h₁₂ : r ∈ Finset.Icc 1 4)
    (h₁₃ : s ∈ Finset.Icc 1 4) :
    p^q + r^s ≤ 83 := by
  have hp1 : p ≥ 1 := by
    simp [Finset.mem_Icc] at h₁₀
    omega
  have hp2 : p ≤ 4 := by
    simp [Finset.mem_Icc] at h₁₀
    omega
  have hq1 : q ≥ 1 := by
    simp [Finset.mem_Icc] at h₁₁
    omega
  have hq2 : q ≤ 4 := by
    simp [Finset.mem_Icc] at h₁₁
    omega
  have hr1 : r ≥ 1 := by
    simp [Finset.mem_Icc] at h₁₂
    omega
  have hr2 : r ≤ 4 := by
    simp [Finset.mem_Icc] at h₁₂
    omega
  have hs1 : s ≥ 1 := by
    simp [Finset.mem_Icc] at h₁₃
    omega
  have hs2 : s ≤ 4 := by
    simp [Finset.mem_Icc] at h₁₃
    omega
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases s
  <;> norm_num at *
  <;> omega