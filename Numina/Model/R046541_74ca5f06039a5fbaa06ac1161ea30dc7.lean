import Mathlib

theorem algebra_90744 (n : ℤ) :
    ∃ m, m^3 = n * (n + 1) * (n + 2) + (n + (n + 1) + (n + 2)) / 3 := by
  use n + 1
  have h1 : (n + (n + 1) + (n + 2) : ℤ) = 3 * (n + 1) := by
    ring
  have h2 : (n + (n + 1) + (n + 2) : ℤ) / 3 = n + 1 := by
    rw [show (n + (n + 1) + (n + 2) : ℤ) = 3 * (n + 1) by linarith]
    simp [Int.mul_ediv_cancel_left]
  rw [h2]
  ring_nf