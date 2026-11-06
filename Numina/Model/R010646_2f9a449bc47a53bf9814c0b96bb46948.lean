import Mathlib

/- g(n+1) = 2^g(n) -/
def g_4508 : ℕ → ℕ
| 0 => default
| 1 => 2
| n + 1 => 2 ^ g_4508 n

theorem number_theory_4508 : g_4508 4 = 65536 := by 
  rfl