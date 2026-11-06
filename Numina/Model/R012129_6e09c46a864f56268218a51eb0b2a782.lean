import Mathlib


theorem number_theory_82657
    {a : ℕ → ℕ} {S : Set ℕ}
    (ha : ∀ n, a n = n ^ 2 + n + 1)
    (hS : S = Set.image a (.univ)) :
    (∀ n, a n * a (n + 1) ∈ S) ∧
    ∃ s t, s ∈ S ∧ t ∈ S ∧ s ≠ t ∧ s * t ∉ S := by
  constructor
  · -- Show that $\forall n, a(n) \cdot a(n + 1) \in S$
    intro n
    have h1 : a n * a (n + 1) ∈ S := by
      rw [hS]
      use n ^ 2 + 2 * n + 1
      simp [ha]
      <;> ring_nf <;> omega
    exact h1
  · -- Two elements $s,t$ of $S$ such that $s\neq t$ and $s \cdot t \notin S$
    use 3, 13
    constructor
    · -- Show that 3 ∈ S
      rw [hS]
      use 1
      simp [ha]
    constructor
    · -- Show that 13 ∈ S
      rw [hS]
      use 3
      simp [ha]
    constructor
    · -- Show that 3 ≠ 13
      norm_num
    · -- Show that 3 * 13 ∉ S
      rw [hS]
      intro h
      rcases h with ⟨k, hk⟩
      simp [ha] at hk
      have h1 : k ≤ 6 := by
        nlinarith
      interval_cases k <;> omega