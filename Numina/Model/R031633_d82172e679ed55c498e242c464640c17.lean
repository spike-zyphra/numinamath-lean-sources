import Mathlib

theorem number_theory_5053 (a : ℕ) (ha : a ≠ 0) :
    ∃ x, a * x ^ 4 ≡ 2 [MOD 13] ↔ a ≡ 2 [MOD 13] ∨ a ≡ 5 [MOD 13] ∨ a ≡ 6 [MOD 13] := by
  have h1 : a % 13 = 2 ∨ a % 13 = 5 ∨ a % 13 = 6 ∨ a % 13 = 1 ∨ a % 13 = 3 ∨ a % 13 = 4 ∨ a % 13 = 7 ∨ a % 13 = 8 ∨ a % 13 = 9 ∨ a % 13 = 10 ∨ a % 13 = 11 ∨ a % 13 = 12 ∨ a % 13 = 0 := by
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h)
  · -- When a ≡ 2 [MOD 13], x = 1 satisfies a * x^4 ≡ 2 [MOD 13].
    use 1
    simp [Nat.ModEq] at *
    omega
  · -- When a ≡ 5 [MOD 13], x = 2 satisfies a * x^4 ≡ 2 [MOD 13].
    use 2
    simp [Nat.ModEq] at *
    omega
  · -- When a ≡ 6 [MOD 13], x = 4 satisfies a * x^4 ≡ 2 [MOD 13].
    use 4
    simp [Nat.ModEq] at *
    omega
  · -- When a ≡ 1 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 3 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 4 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 7 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 8 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 9 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 10 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 11 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 12 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *
  · -- When a ≡ 0 [MOD 13], there's no solution.
    use 0
    simp [Nat.ModEq, Nat.mul_mod, pow_succ, h] at *