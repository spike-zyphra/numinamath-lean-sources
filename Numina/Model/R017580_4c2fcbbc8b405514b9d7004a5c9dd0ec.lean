import Mathlib

theorem algebra_211592 (n : ℕ) (hn : 3 ≤ n) :
    ∃ a : Fin (n + 2) → ℝ, ∀ i : Fin n, a i * a (i + 1) + 1 = a (i + 2) ↔ n = 3 ∨ n = 4 := by

  by_cases hn1 : n = 3
  · -- If n = 3, we prove existence
    rw [hn1]
    use ![-1, 2, -1, -1, 2]
    intro i
    fin_cases i <;> simp [Fin.sum_univ_three, add_assoc] <;> norm_num
    <;> tauto
  · -- n ≠ 3, so n ≥ 4
    have hn4 : n ≥ 4 := by omega
    by_cases hn2 : n = 4
    · -- If n = 4, we prove existence
      rw [hn2]
      use ![-1, 2, -1, -1, 2, -1]
      intro i
      fin_cases i <;> simp [Fin.sum_univ_four, add_assoc] <;> norm_num
      <;> tauto
    · -- n > 4
      have hn5 : n ≥ 5 := by omega
      use fun _ => (0 : ℝ)
      intro i
      simp at *
      all_goals omega