import Mathlib

def u : ℕ → ℤ
| 0 => 1
| 1 => 4
| n + 2 => 5 * u (n + 1) - 6 * u n

theorem algebra_106154 (n : ℕ) : u n = 2 * 3 ^ n - 2 ^ n := by
  match n with
  | 0 =>
    simp [u]
    <;> norm_num
  | 1 =>
    simp [u]
    <;> norm_num
  | n + 2 =>
    have h1 : u (n + 1) = 2 * 3 ^ (n + 1) - 2 ^ (n + 1) := by
      apply algebra_106154
    have h2 : u n = 2 * 3 ^ n - 2 ^ n := by
      apply algebra_106154
    simp [u, h1, h2]
    <;> ring