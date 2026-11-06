import Mathlib

theorem number_theory_197210 (n m : ℕ) (h₀ : n > 0) (h₁ : m > 0)
    (h₂ : ∑ i ∈ Finset.range n, (2 * i + 1) = 1369) (h₃ : ∑ i ∈ Finset.range m, (2 * i + 2) = 2162) :
    n + m = 83 := by

  have h4 : ∀ n : ℕ, ∑ i in Finset.range n, (2 * i + 1 : ℕ) = n ^ 2 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf

  have h5 : n ^ 2 = 1369 := by
    have eq1 := h4 n
    linarith [h₂, eq1]

  have hn : n = 37 := by
    nlinarith

  have h6 : ∀ m : ℕ, ∑ i in Finset.range m, (2 * i + 2 : ℕ) = m * (m + 1) := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf

  have h7 : m * (m + 1) = 2162 := by
    have eq2 := h6 m
    linarith [h₃, eq2]

  have hm : m = 46 := by
    nlinarith [show m ≤ 47 by nlinarith]

  linarith [hn, hm]