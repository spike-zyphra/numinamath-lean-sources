import Mathlib


theorem number_theory_31486 (n : ℕ) (hn : 0 < n) (a b c : ℕ)
    (ha : a ≥ n) (hb : b ≥ n) (hc : c ≥ n)
    (hsum : a + b + c = n * (n + 1) / 2) :
    ∃ s : Finset ℕ, s.card = n ∧
      ∑ i ∈ s, i = a + b + c ∧
      ∀ i ∈ s, i ≤ n := by
  use Finset.Icc 1 n
  constructor
  · -- Show that the cardinality of the set is n.
    simp
  constructor
  · -- Show that the sum of the set equals a + b + c.
    have h1 : ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2 := by
      have h2 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2 := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [ih]
          ring_nf
          omega
      apply h2 n
    rw [h1]
    omega
  · -- Show that all elements in the set are less than or equal to n.
    intro i hi
    have h2 : i ∈ Finset.Icc 1 n := by
      exact hi
    simp at h2 ⊢
    all_goals omega