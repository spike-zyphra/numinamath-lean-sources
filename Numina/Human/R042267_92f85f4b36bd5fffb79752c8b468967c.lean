import Mathlib

/- Find the unique $\textbf{odd}$ integer $t$ such that $0 < t < 23$ and $t+2$ is the inverse of $t$ modulo $23$.-/
theorem number_theory_22771 {t : ℕ} (ht : 0 < t ∧ t < 23) :
    Odd t ∧ t * (t + 2) ≡ 1 [MOD 23] ↔ t = 17 := by
  constructor
  swap
  -- Verify that t=17 satisfies t is odd and t * (t + 2) ≡ 1 [MOD 23].
  . intro h
    rw [h, Nat.odd_iff, Nat.ModEq]
    norm_num
  -- Check t=1,2,...,22 to ensure that only 17 satisfies requirement.
  intro h
  rw [Nat.odd_iff, Nat.ModEq] at h
  rcases ht with ⟨ht1, ht2⟩
  interval_cases t
  any_goals norm_num at h
  norm_num
