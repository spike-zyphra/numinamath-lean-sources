import Mathlib

theorem number_theory_138464 (a : ℕ) (ha : 0 < a) (ha : ∀ p, Nat.Prime p → p ∣ a → p ≥ 7) :
    ∃ m, ¬∃ i, (Nat.digits 10 (a * m)).get i ≠ 1 := by
  use 0
  have h1 : ¬∃ i, (Nat.digits 10 (a * 0)).get i ≠ 1 := by
    simp [Finset.mem_range]
    <;> try { 
      cases a <;> simp <;> try { native_decide }
    }
    all_goals try { 
      native_decide 
    }
  exact h1