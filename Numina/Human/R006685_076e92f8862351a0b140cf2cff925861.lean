import Mathlib
/- Let $K$ be a natural number such that $K \ge 5$. Given four consecutive natural numbers $n, n+1, n+2, n+3$ such that $n > K$. Prove that from these four numbers, one can choose three numbers whose sum can be represented as the product of three distinct natural numbers, each greater than 1. -/
theorem number_theory_640136 (n : ℕ) (A : Finset ℕ) (hn : n > 5) (hA : A = {n, n + 1, n + 2, n + 3}) : ∃ x y z p q r : ℕ, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ p ≠ q ∧ q ≠ r ∧ r ≠ q ∧ p > 1 ∧ q > 1 ∧ r > 1 ∧ x + y + z = p * q * r:= by
  -- Case analysis: check if n equals 6
  by_cases h1 : n = 6
  .
    -- Case 1: n = 6, use the specific example {6,7,8,9}
    subst n
    simp at hA
    subst A
    -- Choose 7, 8, 9 and their product representation 2*3*4 = 24 = 7+8+9
    use 7, 8, 9, 2, 3, 4
    simp
  .
    -- Case 2: n > 6, we have n ≥ 7
    replace hn : n > 6:= by omega
    clear h1
    -- Further case analysis: check if n is odd
    by_cases h1 : Odd n
    .
      -- Case 2a: n is odd, so n = 2k+1 for some k
      rcases h1 with ⟨k, rfl⟩
      ring_nf at hA
      subst A
      -- Choose 2k+1, 2k+2, 2k+3 and represent their sum as 2*3*(k+1)
      use 1 + k * 2, 2 + k * 2, 3 + k * 2, 2, 3, k + 1
      simp
      omega
    .
      -- Case 2b: n is even, so n = 2k for some k
      simp at h1
      rcases h1 with ⟨k, rfl⟩
      ring_nf at hA
      subst A
      -- Choose 2k+1, 2k+2, 2k+3 and represent their sum as 2*3*(k+1)
      use 1 + 2 * k, 2 + k * 2, 3 + k * 2, 2, 3, k + 1
      simp
      omega
