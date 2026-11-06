import Mathlib

theorem number_theory_6745 (a b c d : ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10)
    (h : Nat.ofDigits 10 [a, a, a, a] + Nat.ofDigits 10 [b, b, b, b] + Nat.ofDigits 10 [c, c, c, c] +
      Nat.ofDigits 10 [d, 0, d, d] = 25483) :
    d = 7 := by
  simp [Nat.ofDigits, List.foldl] at h
  all_goals
  interval_cases d <;> omega