import Mathlib.Tactic

theorem number_theory_8424 (s : Finset ℕ) (h₀ : s.card = 5)
    (h₁ : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → Nat.Coprime m n)
    (h₂ : ∀ m ∈ s, m ∈ Finset.Icc 100 999) :
    ∃ t ⊆ s, t.card = 4 ∧ ∀ m ∈ t, ∀ n ∈ t, m ≠ n → Nat.Coprime m n := by

  have h3 : s.card = 5 := h₀
  have h4 : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [h] at h3
    simp at h3

  rcases h4 with ⟨a, ha⟩
  have h6 : (s.erase a).card = 4 := by
    have h7 : a ∈ s := ha
    have h8 : s.card = 5 := h₀
    rw [Finset.card_erase_of_mem h7]
    omega

  use s.erase a
  constructor
  · -- t ⊆ s
    apply Finset.erase_subset
  constructor
  · -- t.card = 4
    exact h6
  · -- Show that all elements in t are pairwise coprime
    intro m hm n hn hneq
    have h13 : m ∈ s := by
      apply Finset.mem_of_mem_erase hm
    have h14 : n ∈ s := by
      apply Finset.mem_of_mem_erase hn
    have hneq2 : m ≠ n := by
      exact hneq
    apply h₁ m h13 n h14 hneq2