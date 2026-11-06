import Mathlib
open BigOperators

/- 9В In a rectangular table, the product of the sum of the numbers in any column and the sum of the numbers in any row equals the number at their intersection.

Prove that the sum of all numbers in the table is one, or all numbers are zero.

# -/
theorem algebra_216065 {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (h : ∀ i j, a i j = (∑ k : Fin n, a i k) * (∑ l : Fin m, a l j)) :
    (∑ i, ∑ j : Fin n, a i j = 1) ∨ (∀ i, ∀ j, a i j = 0) := by
    -- write x i for the sum of the numbers in the ith row
    -- and y j for the sum of the numbers in the jth column
    -- then x i = x i * (y 1 + ... + y n)
    have : ∀ i, ∑ j : Fin n, a i j = (∑ k : Fin n, a i k) * (∑ k, ∑ l : Fin m, a l k)
    · intro i
      calc
        ∑ j : Fin n, a i j = ∑ j : Fin n, (∑ k : Fin n, a i k) * (∑ l : Fin m, a l j) := by conv_lhs => arg 2; intro j; rw [h i j]
        _ = (∑ k : Fin n, a i k) * (∑ k, ∑ l : Fin m, a l k) := by rw [Finset.mul_sum]
    -- so either y 1 + ... + y n = 1 or x i = 0
    conv at this => intro i; rw [eq_comm, mul_right_eq_self₀]
    rw [forall_or_left] at this
    cases' this with h1 h0
    -- in the first case, this is the sum of all the numbers in the table and we're done
    · left
      rw [←h1]
      exact Finset.sum_comm
    -- in the second case, we have a i j = x i * y j, so a i j = 0
    · right
      intro i j
      specialize h0 i
      specialize h i j
      rw [h0, zero_mul] at h
      exact h