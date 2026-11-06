import Mathlib

theorem number_theory_242789 (n : ℕ) :
    n ∈ {n | n ∈ Finset.Ico 100 550 ∧ (n / 100) % 10 = (n / 10) % 10 * (n % 10)} ↔
    n = 111 ∨ n = 212 ∨ n = 221 ∨ n = 313 ∨ n = 331 ∨ n = 414 ∨ n = 441 ∨ n = 422 ∨ n = 515 := by
  constructor
  · -- First implication: if n is in the left side, then it's in the right side
    intro hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Ico] at hn1
    rcases hn1 with ⟨hn10, hn11⟩
    interval_cases n <;> norm_num at hn2 ⊢ <;> tauto
  · -- Second implication: if n is in the right side, then it's in the left side
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      constructor
      · -- Show that n is in the interval [100, 550)
        native_decide
      · -- Show the digit property
        all_goals
          native_decide