import Mathlib

/-
Given four consecutive natural numbers greater than 100. Prove that from these numbers, one can choose three numbers whose sum can be represented as the product of three different natural numbers greater than 1.
-/
theorem number_theory_101609 (n : ℕ) (h₀ : n > 100) :
    ∃ a b c, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ a > 1 ∧ b > 1 ∧ c > 1 ∧
      (a * b * c = n + (n + 1) + (n + 2)) ∨
      (a * b * c = n + (n + 1) + (n + 3)) ∨
      (a * b * c = n + (n + 2) + (n + 3)) ∨
      (a * b * c = (n + 1) + (n + 2) + (n + 3))
  := by
  -- Either n is even or n is odd
  obtain (even | odd) := Nat.even_or_odd n
  · -- If n is even, it can be written as the product of k and two
    obtain ⟨ k, two_k ⟩ := even
    -- Choose a, b, and c whose product equals (n + 1) + (n + 2) + (n + 3)
    use 3, 2, k + 1
    -- Simplify
    omega
  · -- Write n as a multiple plus one
    obtain ⟨ k, two_k1 ⟩ := odd
    -- Choose a, b, and c whose product equals n + (n + 1) + (n + 2)
    use 3, 2, k + 1
    -- Simplify
    omega