import Mathlib

def u : ℕ → ℤ
| 0 => 2
| 1 => 3
| n + 2 => 3 * u (n + 1) - 2 * u n

theorem algebra_116060 {n} : u n = 2 ^ n + 1 := by 
  match n with
  | 0 => 
    simp [u]
  | 1 => 
    simp [u]
  | n + 2 => 
    have h1 : u n = 2 ^ n + 1 := by 
      apply algebra_116060
    have h2 : u (n + 1) = 2 ^ (n + 1) + 1 := by 
      apply algebra_116060
    simp [u, h1, h2]
    <;> ring_nf <;> omega