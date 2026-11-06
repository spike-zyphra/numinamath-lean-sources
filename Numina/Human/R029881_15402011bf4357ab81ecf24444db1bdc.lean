import Mathlib

/- define the answer to the problem -/
abbrev Solution_4853 : ℕ → ℕ := fun n => match n with
  | 13 => 12
  | 14 => 6
  | 15 => 8
  | 16 => 8
  | 17 => 16
  | 18 => 6
  | 19 => 18
  | 20 => 8
  | _ => 0

/- Find the value of the Euler's totient function \(\phi(n)\) for the integers \(n\) in the range from 13 to 20, inclusive.-/
theorem number_theorey_4853 : ∀ n, 13 ≤ n ∧ n ≤ 20 → (Nat.totient n = Solution_4853 n) := by
  -- check the answer
  intro n hn
  have hn:n=13 ∨ n=14 ∨ n=15 ∨ n=16 ∨ n=17 ∨ n=18 ∨ n=19 ∨ n=20 := by omega
  -- check the cases
  aesop
