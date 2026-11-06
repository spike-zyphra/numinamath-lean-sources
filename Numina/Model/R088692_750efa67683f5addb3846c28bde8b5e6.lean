import Mathlib

theorem algebra_274488 (m n : ℕ) (h₀ : 0 < m) (h₁ : 0 < n) (h₂ : n^2 - m^2 > 20)
    (h₃ : m + 1 = n) :
    n^2 + m^2 ≥ 221 := by
  have h4 : n = m + 1 := by omega
  have h5 : n ^ 2 - m ^ 2 = 2 * m + 1 := by
    rw [h4]
    ring_nf
    <;> omega
  have h6 : 2 * m + 1 > 20 := by 
    have : n ^ 2 - m ^ 2 > 20 := h₂
    omega
  -- From h6: 2 * m + 1 > 20 → 2 * m + 1 ≥ 21, so 2 * m ≥ 20
  have h7 : m ≥ 10 := by
    omega
  -- n ≥ 11 since n = m + 1 and m ≥ 10
  have hn : n ≥ 11 := by
    omega
  -- Calculation n^2 + m^2 ≥ 11^2 + 10^2 = 221
  nlinarith [h7, hn, h4]