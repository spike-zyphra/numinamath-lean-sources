import Mathlib

theorem number_theory_70352 (n r : ℕ) (h : ∀ k : ℕ, ¬(∃ m : ℤ, m = n ^ 2 + r - k * (k + 1) ∧ m = -1 ∨ m > 0 ∧ ¬Prime m)) :
    4 * n ^ 2 + 4 * r + 1 = 1 ∨ 4 * n ^ 2 + 4 * r + 1 = 9 ∨ Prime (4 * n ^ 2 + 4 * r + 1) := by
  specialize h 0
  have h1 : ∃ m : ℤ, m = n ^ 2 + r - 0 * (0 + 1) ∧ m = -1 ∨ m > 0 ∧ ¬Prime m := by
    use 1
    norm_num at *
    <;> try { tauto }
  contradiction