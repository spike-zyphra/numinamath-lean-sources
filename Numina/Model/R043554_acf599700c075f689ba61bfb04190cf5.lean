import Mathlib


theorem number_theory_260032 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ∃ a : ℕ, (p * q) / (p + q) = (a ^ 2 + 1) / (a + 1) ↔ p = 5 ∧ q = 2 := by
  by_cases h : p = 5 ∧ q = 2
  · -- p = 5 and q = 2
    rcases h with ⟨hp', hq'⟩
    use 1
    all_goals
    simp [hp', hq']
  · -- p ≠ 5 or q ≠ 2
    by_cases h2 : (p * q) / (p + q) = 1
    · -- (p * q) / (p + q) = 1
      use 3
      simp [h2]
      all_goals
      try { tauto }
    · -- (p * q) / (p + q) ≠ 1
      use 0
      simp at h2 ⊢
      all_goals
      try { tauto }