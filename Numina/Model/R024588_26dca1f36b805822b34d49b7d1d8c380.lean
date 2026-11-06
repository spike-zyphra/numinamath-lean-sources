import Mathlib

theorem number_theory_158554 (n : ℕ) (hn : n > 0) :
    (Nat.card {x | ∃ n : ℕ, x = 7 * n + 1 ∧ x ≤ 6 * n}) / (6 * n) = 5 / 11 := by
  have h1 : {x | ∃ n : ℕ, x = 7 * n + 1 ∧ x ≤ 6 * n} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨n, hn1, hn2⟩
    have h2 : 7 * n + 1 > 6 * n := by
      omega
    have h3 : 7 * n + 1 ≤ 6 * n := by
      omega
    omega
  rw [h1]
  simp at *
  <;> linarith