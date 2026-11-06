import Mathlib

/- Theorem: Let $n$ be a three-digit natural number. Let $S(k)$ denote the sum of the decimal digits of $k$. Let $n_1 = n + S(n)$, and let $n_2 = n_1 + S(n_1)$. It is required that $n_2$ is the number obtained by reversing the digits of $n$, and that $n_2$ is also a three-digit number. Show that there are no such three-digit numbers $n$. -/
theorem number_theory_634646 {n n₁ n₂ : ℕ} (hn : (Nat.digits 10 n).length = 3) (hn₁ : n₁ = n + (Nat.digits 10 n).sum) (hn₂ : n₂ = n₁ + (Nat.digits 10 n₁).sum) (hn₂' : Nat.digits 10 n₂ = (Nat.digits 10 n).reverse) (hn₂'' : (Nat.digits 10 n₂).length = 3) : False := by
  -- n₂ is clearly a three-digit number, so we can remove the condition.
  clear hn₂''
  -- We can substitute n₁ and n₂.
  subst n₁ n₂
  -- We rewrite the condition that n is a three-digit number to be a membership in the interval [100, 1000).
  replace hn : n ∈ Finset.Ico 100 1000 := by
    -- Use the formula for the number of digits of a number.
    rw [Nat.digits_len _ _ (by simp) (by rintro rfl; simp at hn)] at hn
    -- Simplify using `Nat.log_eq_iff`.
    simp only [Nat.reduceEqDiff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.one_lt_ofNat,
      true_and, true_or, Nat.log_eq_iff, Nat.reducePow, Nat.reduceAdd] at hn
    exact Finset.mem_Ico.mpr hn
  -- We now quantify over `n`.
  revert hn₂'
  revert n
  -- We can use `native_decide` to check all possible cases of `n`.
  native_decide