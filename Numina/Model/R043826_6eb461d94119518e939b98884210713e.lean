import Mathlib

theorem number_theory_273227 (a b c d n : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c) (h₃ : 0 < d)
    (h₄ : a ≠ b) (h₅ : a ≠ c) (h₆ : a ≠ d) (h₇ : b ≠ c) (h₈ : b ≠ d) (h₉ : c ≠ d)
    (h₁₀ : a + b + c + d = 100) (h₁₁ : max (max a b) (max c d) = n) :
    n ≥ 27 := by
  by_contra h
  push_neg at h
  have h12 : a ≤ 26 := by
    have h13 : a ≤ n := by
      have h14 : a ≤ max (max a b) (max c d) := by
        simp [max_le_iff]
        all_goals omega
      rw [h₁₁] at h14
      omega
    omega
  have h13 : b ≤ 26 := by
    have h14 : b ≤ n := by
      have h15 : b ≤ max (max a b) (max c d) := by
        simp [max_le_iff]
        all_goals omega
      rw [h₁₁] at h15
      omega
    omega
  have h14 : c ≤ 26 := by
    have h15 : c ≤ n := by
      have h16 : c ≤ max (max a b) (max c d) := by
        simp [max_le_iff]
        all_goals omega
      rw [h₁₁] at h16
      omega
    omega
  have h15 : d ≤ 26 := by
    have h16 : d ≤ n := by
      have h17 : d ≤ max (max a b) (max c d) := by
        simp [max_le_iff]
        all_goals omega
      rw [h₁₁] at h17
      omega
    omega
  have h16 : n ≤ 26 := by linarith
  have h17 : a + b + c + d ≤ 98 := by 
    have h18 : a ≤ 26 := by linarith
    have h19 : b ≤ 26 := by linarith
    have h20 : c ≤ 26 := by linarith
    have h21 : d ≤ 26 := by linarith
    omega
  omega