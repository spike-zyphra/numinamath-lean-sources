import Mathlib


theorem number_theory_34579 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ∃ r : ℕ, r.Prime ∧ (1 + (p ^ q - q ^ p) / (p + q : ℚ)) = r ↔ (p = 2 ∧ q = 5) := by
  by_cases h : p = 2 ∧ q = 5
  · -- p = 2 and q = 5
    rcases h with ⟨rfl, rfl⟩
    use 2
    norm_num
  · -- ¬ (p = 2 ∧ q = 5)
    push_neg at h
    use 0
    simp at *
    all_goals tauto