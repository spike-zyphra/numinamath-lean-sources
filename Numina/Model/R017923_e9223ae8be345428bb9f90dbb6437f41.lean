import Mathlib

theorem number_theory_187800 :
    (∀ n : ℕ, Even n → Even (∑ i in Finset.range n, (2 * i + 2))) ∧
    (∀ n : ℕ, Even n → Even (∑ i in Finset.range n, (2 * i + 1))) ∧
    (∀ n : ℕ, Odd n → Even (∑ i in Finset.range n, (2 * i + 2))) ∧
    (∀ n : ℕ, Odd n → Odd (∑ i in Finset.range n, (2 * i + 1))) := by
  constructor
  · -- Proof for (a) even n → even (∑ i in range n, (2 * i + 2))
    intro n hn
    have h1 : ∀ n : ℕ, (∑ i in Finset.range n, (2 * i + 2) ) = n * (n + 1) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have h2 : (∑ i in Finset.range n, (2 * i + 2) ) = n * (n + 1) := h1 n
    rw [h2]
    rcases hn with ⟨m, hm⟩
    rw [hm]
    use m * (2 * m + 1)
    ring_nf
  constructor
  · -- Proof for (b) even n → even (∑ i in range n, (2 * i + 1))
    intro n hn
    have h1 : ∀ n : ℕ, (∑ i in Finset.range n, (2 * i + 1) ) = n ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring_nf
    have h2 : (∑ i in Finset.range n, (2 * i + 1) ) = n ^ 2 := h1 n
    rw [h2]
    rcases hn with ⟨m, hm⟩
    use 2 * m ^ 2
    rw [hm]
    all_goals ring_nf
    <;> norm_num
  constructor
  · -- Proof for (c) odd n → even (∑ i in range n, (2 * i + 2))
    intro n hn
    have h1 : ∀ n : ℕ, (∑ i in Finset.range n, (2 * i + 2) ) = n * (n + 1) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have h2 : (∑ i in Finset.range n, (2 * i + 2) ) = n * (n + 1) := h1 n
    rw [h2]
    rcases hn with ⟨m, hm⟩
    rw [hm]
    use (m + 1) * (2 * m + 1)
    ring_nf
  · -- Proof for (d) odd n → odd (∑ i in range n, (2 * i + 1))
    intro n hn
    have h1 : ∀ n : ℕ, (∑ i in Finset.range n, (2 * i + 1) ) = n ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring_nf
    have h2 : (∑ i in Finset.range n, (2 * i + 1) ) = n ^ 2 := h1 n
    rw [h2]
    rcases hn with ⟨m, hm⟩
    use 2 * m ^ 2 + 2 * m
    rw [hm]
    all_goals ring_nf
    <;> norm_num