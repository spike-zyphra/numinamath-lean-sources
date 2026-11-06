import Mathlib

/- g(n+1) = 2^g(n) -/
def g_4508 : ℕ → ℕ
| 0 => default
| 1 => 2
| n + 1 => 2 ^ g_4508 n

/- Let \( g \) be a function defined recursively such that \( g(1) = 2 \) and for \( n \geq 2 \),
  \( g(n) = 2^{g(n-1)} \). We need to find the value of \( g(4) \).-/
theorem number_theory_4508 : g_4508 4 = 65536 := rfl
