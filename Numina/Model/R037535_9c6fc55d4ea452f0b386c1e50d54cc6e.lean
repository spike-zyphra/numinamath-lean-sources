import Mathlib

theorem number_theory_200519 (d : ℤ) : ∃ m n, d = (n - 2 * m + 1) / (m ^ 2 - n) := by
  by_cases h : d = -1
  · -- If d = -1, then m = 1, n = 2 is a solution
    use 1, 2
    norm_num [h]
  · -- If d ≠ -1
    have hd1 : d ≠ -1 := h
    have h2 : d + 1 ≠ 0 := by
      intro h1
      have : d = -1 := by linarith
      contradiction
    use d + 2, d^2 + 3 * d + 3
    have h_eq : ((d^2 + 3 * d + 3) - 2 * (d + 2) + 1 : ℤ) = d * (d + 1) := by
      nlinarith
    have h_denom : ((d + 2) ^ 2 - (d^2 + 3 * d + 3) : ℤ) = (d + 1) := by
      nlinarith
    rw [h_eq, h_denom]
    have h4 : (d + 1 : ℤ) ≠ 0 := h2
    field_simp [h4]
    <;> nlinarith