import Mathlib

/- Lemma 1: A number has four digits if and only if it is between 1000(inclusive) and 10000(exclusive). -/
lemma lemma_1 (n : ℕ) :
    (Nat.digits 10 n).length = 4 ↔ 1000 ≤ n ∧ n < 10000 := by
  by_cases hn : n = 0
  . simp [hn]
  simp [Nat.digits_len 10 n (by simp) hn]
  rw [Nat.log_eq_iff (by simp)]

/- Example 3 If the digits of a four-digit number are reversed to form a new four-digit number, the new number is exactly four times the original number. Find the original number.
(1988, Nanjing Mathematical Olympiad Selection Contest) -/
theorem number_theory_299554 :
    {n | (Nat.digits 10 n).length = 4 ∧ Nat.ofDigits 10 ((Nat.digits 10 n).reverse) = 4 * n} = {2178} := by
  -- By lemma 1, we have the set is equal to the finset of numbers between 1000(inclusive) and 10000(exclusive) that satisfies the condition.
  have H : { n | (Nat.digits 10 n).length = 4 ∧ Nat.ofDigits 10 ((Nat.digits 10 n).reverse) = 4 * n } = { n ∈ Finset.Ico 1000 10000 | Nat.ofDigits 10 ((Nat.digits 10 n).reverse) = 4 * n } := by
    ext n
    simp [lemma_1]
  -- Cast to finset.
  rw [H, show ({2178} : Set ℕ) = ({2178} : Finset ℕ) by simp]
  norm_cast
  -- Now the equality between finsets is decidable.
  native_decide
