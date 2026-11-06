import Mathlib

theorem algebra_11970 {x : ℝ} (h : abs (x - 20) + abs (x - 18) = abs (2 * x - 36)) : x = 19 := by
  have h1 : abs (2 * x - 36) = 2 * abs (x - 18) := by
    calc
      abs (2 * x - 36) = abs (2 * (x - 18)) := by ring_nf
      _ = abs (2) * abs (x - 18) := by rw [abs_mul]
      _ = 2 * abs (x - 18) := by norm_num
  rw [h1] at h
  have h2 : abs (x - 20) = abs (x - 18) := by linarith
  cases abs_eq_abs.1 h2 with
  | inl h3 =>
      linarith
  | inr h4 =>
      linarith