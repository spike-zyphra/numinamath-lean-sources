import Mathlib

theorem number_theory_1290 (a : Fin 3 → ℕ) (ha : ∃ n, a = ![n, n + 1, n + 2]) : ∀ i, a i > 0 → a 1 ^ 3 ∣ a 0 * a 1 * a 2 + a 1 := by
  intro i hi
  rcases ha with ⟨n, hn⟩
  have eq1 : a 0 = n := by 
    simp [hn]
  have eq2 : a 1 = n + 1 := by 
    simp [hn]
  have eq3 : a 2 = n + 2 := by 
    simp [hn]
  rw [eq1, eq2, eq3] 
  use 1
  all_goals 
    ring_nf
    all_goals
      omega