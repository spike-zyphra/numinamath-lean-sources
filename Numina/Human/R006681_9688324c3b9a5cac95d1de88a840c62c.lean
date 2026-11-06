import Mathlib

/-Let $X$ be a positive integer. Determine all four-digit numbers $n$ (written in base 10) such that $n$ is divisible by $X$, and the quotient $n/X$ is equal to the sum of the digits of $n$. Show that for $X=75$, the set of such numbers is empty.-/
theorem number_theory_640028 (X : ℕ) (hX : X = 75) : {n : ℕ | 1000 ≤ n ∧ n < 10000 ∧ X ∣ n ∧ n / X = (Nat.digits 10 n).sum} = ∅ := by
  suffices {n | 1000 ≤ n ∧ n < 10000 ∧ X ∣ n ∧ n / X = (Nat.digits 10 n).sum} = Finset.filter (λn ↦ 75 ∣ n ∧ n / 75 = (Nat.digits 10 n).sum) (Finset.Ico 1000 10000) by
    rw [this]
    apply Finset.coe_eq_empty.mpr
    native_decide
  simp only [Nat.reduceLeDiff, Finset.coe_filter, Finset.mem_Ico, hX]
  ext x; simp only [Nat.reduceLeDiff, Set.mem_setOf_eq]
  tauto
