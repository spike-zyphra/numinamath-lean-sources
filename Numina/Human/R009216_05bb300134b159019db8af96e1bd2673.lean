import Mathlib

/- define the answer to the problem -/
def Solution : ℕ → ℕ := fun n => match n with
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 6 => 2
  | 14 => 6
  | 24 => 8
  | n => Nat.totient n

/- Find all positive integers \( n \) such that the Euler's totient function \( \phi(n) \) takes the following values:
a) 1
b) 2
c) 3
d) 6
e) 14
f) 24-/
theorem number_theory_4864 : (n=1 ∨ n=2 ∨ n=3 ∨ n=6 ∨ n=14 ∨ n=24) →
    (Nat.totient n = Solution n) := by
  intro h
  aesop
