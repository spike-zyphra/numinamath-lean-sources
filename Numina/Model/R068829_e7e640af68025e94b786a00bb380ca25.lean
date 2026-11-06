import Mathlib
open Nat

theorem algebra_1451 {n : ℕ} (h : n < 100) (h1 : n > 9)
(h2 : 3 * (n % 10 + n / 10) - 2 = n) : n = 28 := by
  interval_cases n <;> omega