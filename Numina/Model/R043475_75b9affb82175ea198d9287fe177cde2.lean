import Mathlib

theorem number_theory_36743 (p : ℕ) (hp : Odd p ∧ Nat.Prime p)
    (A : ℕ → ℕ) (hA : ∀ n, A n = {s : Finset ℕ | s ⊆ Finset.Icc 1 n ∧ p ∣ ∑ x ∈ s, x}.ncard) (hB : ¬p ^ 2 ∣ 2 ^ (p - 1) - 1):
    ∀ k, ∃ m > k, ∃ z : ℤ, (A m - k) / p = z := by
  intro k
  use k + 1
  constructor
  · -- Show m > k
    omega
  · -- Show there exists integer z s.t. (A m - k) / p = z
    refine' ⟨(A (k + 1) - k) / p, by
      simp
    ⟩