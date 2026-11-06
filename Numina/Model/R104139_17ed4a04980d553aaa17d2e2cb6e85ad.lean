import Mathlib

theorem algebra_202779 (m n : ℤ) (h₀ : 0 < m) (h₁ : 0 < n)
    (h₂ : m^2 - n^2 = 43) : m^3 - n^3 = 1387 := by
  have h3 : m^2 - n^2 = (m - n) * (m + n) := by
    ring
  rw [h3] at h₂
  have h4 : (m - n) * (m + n) = 43 := h₂
  have h5 : m > n := by
    nlinarith [show m^2 > n^2 from by linarith, h₀, h₁]
  have h6 : m - n = 1 ∨ m - n = 43 := by
    have h7 : (m - n) ∣ 43 := by
      use (m + n)
      linarith
    have h8 : (m - n) ≤ 43 := by
      apply Int.le_of_dvd (by norm_num) h7
    have h9 : (m - n) > 0 := by linarith
    have h10 : (m - n) = 1 ∨ (m - n) = 43 := by 
      interval_cases h : m - n <;> omega
    exact h10
  rcases h6 with (h12 | h12)
  · -- Case 1: m - n = 1, then m + n = 43
    have h13 : m + n = 43 := by 
      rw [h12] at h4
      linarith
    have h14 : m = 22 := by
      linarith [h12, h13]
    have h15 : n = 21 := by 
      linarith [h12, h13]
    rw [h14, h15]
    norm_num
  · -- Case 2: m - n = 43, leads to a contradiction
    have h16 : m + n = 1 := by 
      rw [h12] at h4
      linarith
    have h17 : m + n ≥ 2 := by
      linarith [h₀, h₁]
    linarith