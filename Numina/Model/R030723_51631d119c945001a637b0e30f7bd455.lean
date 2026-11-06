import Mathlib

theorem number_theory_158965 (n : ℕ) :
    {a | 0 < n^6 + 3 * a}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  use a + 1
  have h1 : a < a + 1 := by omega
  have h2 : 0 < n^6 + 3 * (a + 1) := by
    have eq1 : n^6 + 3 * (a + 1) = n^6 + 3 * a + 3 := by omega
    rw [eq1]
    all_goals
      have : n^6 + 3 * a + 3 > 0 := by
        omega
      linarith
  simp at *
  all_goals
    omega