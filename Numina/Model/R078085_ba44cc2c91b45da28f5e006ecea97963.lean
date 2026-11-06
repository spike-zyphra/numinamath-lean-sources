import Mathlib

theorem number_theory_152009 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) (h₁ : (n / 10) * 100 + (n % 10) = n + 720) :
    n ∈ Finset.Icc 80 89 := by
  rw [Finset.mem_Icc] at h₀ ⊢
  rcases h₀ with ⟨h₂, h₃⟩
  have h4 : n ≥ 10 := h₂
  have h5 : n ≤ 99 := h₃
  have h6 : n ≥ 80 := by
    by_contra h
    push_neg at h
    have h6 : n < 80 := by
      omega
    interval_cases n <;> norm_num at h₁ ⊢
    <;> try { try { tauto } <;> omega <;> try { exfalso <;> try omega <;> try { trivial } } }
    <;> try { trivial }
    all_goals try { try { tauto } <;> try { try { trivial } } }
  have h7 : n ≤ 89 := by
    by_contra h
    push_neg at h
    have h8 : n ≥ 90 := by
      omega
    interval_cases n <;> norm_num at h₁ ⊢
    <;> try { try { tauto } <;> omega <;> try { exfalso <;> try omega <;> try { trivial } } }
    <;> try { trivial }
    all_goals try { try { tauto } <;> try { try { trivial } } }
  constructor
  · omega
  · omega