import Mathlib

/-
Let $A$ be a natural number such that $A \geq 2$. Let $m$ and $n$ be fixed natural numbers.
Consider the statement: "There are no natural numbers $k,l$, not both zero, such that $k m + l n = A (k n + l m)$."
Show that this statement is true if $m=1$ and $n=A-1$.
-/

theorem number_theory_638044 (A m n :ℕ) (hA: 2 ≤ A) (hm: m = 1) (hn: n = A - 1):
  ¬ (∃k:ℕ, ∃l:ℕ, k ≠ 0 ∧ l ≠ 0 ∧ k * m + l * n = A * (k * n + l * m)) := by

  --Suppose for contradiction that there is such a pair (k,l).
  by_contra exi
  obtain ⟨k,l, kne0, lne0, h⟩ := exi

  zify at h
  rw [hm, hn] at h
  have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (A - 1) = A - 1 := by omega
  rw [this] at h
  
  --We get k-l = k*A*(A-1). The left-handed side is smaller than k, while the right-handed side is at least k. 
  have eq : (k:ℤ) - l = k * A * (A-1) := by 
    ring_nf at h ⊢
    nlinarith
  
  have l1 : (k:ℤ) - l < k := by omega

  have l2 : (k:ℤ) ≤ k * A * (A-1) := by
    have : 2 ≤ (A:ℤ) * (A-1) := by nlinarith
    nlinarith
  linarith
  