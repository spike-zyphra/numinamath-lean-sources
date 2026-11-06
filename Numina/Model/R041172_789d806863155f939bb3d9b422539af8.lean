import Mathlib

theorem number_theory_9529 (a b c d : ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10)
    (h : Nat.ofDigits 10 [d, c, a, b] + Nat.ofDigits 10 [d, a, b, c] +
      Nat.ofDigits 10 [b, a, c, d] + Nat.ofDigits 10 [c, b, d, a] =
    Nat.ofDigits 10 [5, 5, 5, 5, 2]) :
    a + b + c + d = 23 := by 
  simp [Nat.ofDigits, List.foldl] at h ⊢
  have h1 : a ≤ 9 := by linarith
  have h2 : b ≤ 9 := by linarith
  have h3 : c ≤ 9 := by linarith
  have h4 : d ≤ 9 := by linarith
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega