import Mathlib

/- Show that for any natural number n, n^3 + (n + 1)^3 + (n + 2)^3 is divisible by 9. -/
theorem number_theory_84195 (n : ℕ) : 9 ∣ n^3 + (n + 1)^3 + (n + 2)^3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n + 1)^3 + (n + 2)^3 + (n + 3)^3 = (n + 1)^3 + (n + 2)^3 + (n^3 + 3 * n^2 * 3 + 3 * n * 3^2 + 3^3) := by
      ring
    rw [h]
    norm_num
    omega