import Mathlib

theorem number_theory_18579 :
    {a : ℕ | 0 ≤ a ∧ a < 100 ∧ ∃ x, a * x ≡ 1 [MOD 20] ∧ ∃ y, (a - 1) * y ≡ 1 [MOD 20] ∧ a * y ≡ 4 * x [MOD 20]} = ∅ := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
  intro h
  rcases h with ⟨ha0, ha100, ⟨x, h1, ⟨y, h2, h3⟩⟩⟩
  interval_cases a <;> simp [Nat.ModEq] at h1 h2 h3
  <;> omega