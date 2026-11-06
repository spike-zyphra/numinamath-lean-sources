import Mathlib

theorem number_theory_148645 (n : ℕ) (hn : 1 ≤ n) :
    ∃ q : ℚ, q < 1 ∧ ¬∃ s : Fin n → ℕ, (∀ i, 0 < s i) ∧ q = ∑ i, (1 : ℚ) / s i := by
  use (0 : ℚ)
  constructor
  · -- Show that 0 < 1
    norm_num
  · -- Show that 0 is not the sum of reciprocals of n positive integers
    intro h
    rcases h with ⟨s, hs_pos, heq⟩
    have h1 : ∑ i : Fin n, (1 : ℚ) / (s i) > 0 := by
      apply Finset.sum_pos
      · -- Show that each reciprocal is positive
        intro i hi
        have : (s i : ℚ) > (0 : ℚ) := by exact_mod_cast (hs_pos i)
        positivity
      · -- Show that sum non-empty
        have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
          use ⟨0, by omega⟩
          all_goals simp [Finset.mem_univ]
        simpa using h_nonempty
    linarith [heq, h1]