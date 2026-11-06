import Mathlib

theorem number_theory_138098 (b : ℕ) (hb : b > 6) :
    ∃ p k, p.Prime ∧ p^k = Nat.ofDigits b [4, 5, 6, 5] ↔ b = 7 := by
  by_cases h : b > 7
  · -- Assume b > 7
    use 0
    use 0
    simp [h, Nat.ofDigits, List.foldl]
    all_goals omega
  · -- Assume b ≤ 7
    have h2 : b = 7 := by
      omega
    rw [h2]
    use 2
    use 11
    native_decide