import Mathlib

theorem number_theory_13366 (a b c N : ℕ) (habc : ∃ n, Nat.digits 10 n = [c, b, a])
    (hN : N = Nat.ofDigits 10 [b, c, a] + Nat.ofDigits 10 [a, c, b] +
    Nat.ofDigits 10 [c, a, b] + Nat.ofDigits 10 [b, a, c] + Nat.ofDigits 10 [a, b, c]) :
    N = 3194 → Nat.ofDigits 10 [c, b, a] = 358 := by
  intro h
  simp [Nat.ofDigits, List.foldl] at hN ⊢
  omega