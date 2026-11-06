import Mathlib

/- Find the least positive integer $m$ such that $lcm(15,m) = lcm(42,m)$. Here $lcm(a, b)$ is the least common multiple of $a$ and $b$. -/
theorem number_theory_53999 :
    IsLeast {m : ℕ | 0 < m ∧ Nat.lcm 15 m = Nat.lcm 42 m} 70 := by 
  -- Sequential judgment begins, starting with basic property justifications and checking:
  refine' ⟨by decide, fun m => _⟩
  rintro ⟨h1, h2⟩
  -- Check the set conditions:
  apply Nat.le_of_not_lt
  intro h
  revert h1 h2
  revert m
  decide