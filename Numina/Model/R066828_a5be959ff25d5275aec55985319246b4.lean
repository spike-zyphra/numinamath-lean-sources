import Mathlib

theorem number_theory_276042 : ¬(IsLeast {p | p.Prime} 3) := by
  intro h
  have h1 : 3 ∈ {p | p.Prime} := h.1
  have h2 : ∀ p, p ∈ {p | p.Prime} → 3 ≤ p := h.2
  have h3 := h2 2 (by norm_num)
  norm_num at h3
  all_goals norm_num at h1 ⊢
  all_goals contradiction