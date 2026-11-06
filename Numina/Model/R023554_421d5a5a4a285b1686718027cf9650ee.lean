import Mathlib

theorem inequalities_126053 (n : ℕ) (h₀ : n > 0) (h₁ : (n * 3 + 1) / (n + 1) ≤ 3) :
    (n * 4 + 3) / (n + 1) ≤ 4 := by
  have h4 : n + 1 > 0 := by omega
  have h5 : n * 4 + 3 ≤ 4 * (n + 1) := by
    omega
  have h6 : (n * 4 + 3) / (n + 1) ≤ 4 := by
    apply Nat.div_le_of_le_mul
    linarith
  linarith