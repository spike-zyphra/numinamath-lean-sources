import Mathlib

theorem number_theory_274983 (p q : ℤ) (hp : Odd p) (hq : Even q) :
    Odd (3 * p + 2 * q) := by 
  rcases hp with ⟨k, hk⟩
  rcases hq with ⟨m, hm⟩
  use 3 * k + 2 * m + 1 
  rw [hk, hm]
  ring