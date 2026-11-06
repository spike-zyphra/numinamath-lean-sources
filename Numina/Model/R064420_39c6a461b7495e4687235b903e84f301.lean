import Mathlib

theorem number_theory_8003 : ∃ p, p.Prime ∧ p = 10613 ∧ p ∣ 104060465 := by
  use 10613
  constructor
  · -- Check that 10613 is prime.
    norm_num
    -- Lean is proving 10613 is prime. If Lean claims it's a prime, it's proven through computational verification.
    all_goals native_decide
  constructor
  · -- p = 10613, which is trivial
    rfl
  · -- Check that 10613 divides 104060465.
    norm_num