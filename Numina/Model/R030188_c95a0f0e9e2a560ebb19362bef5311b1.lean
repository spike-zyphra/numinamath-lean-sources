import Mathlib

theorem number_theory_82607 (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : Fin (n + 1) → ℚ, (∀ i, ¬∃ m : ℤ, x i = m) ∧
      (∑ i : Fin n, (x i)^3 % 1) = (x n)^3 % 1 := by 
  use fun i => (1 : ℚ) / (2 : ℚ)
  constructor
  · -- Show that ∀ i, ¬∃ m : ℤ, x i = m 
    intro i
    by_contra h
    rcases h with ⟨m, hm⟩
    have h1 : (1 : ℚ) / 2 = (m : ℚ) := by simpa using hm
    have h2 : 1 = 2 * m := by 
      have h2 : (1 : ℚ) / 2 = (m : ℚ) := h1
      have : (1 : ℚ) = 2 * (m : ℚ) := by linarith [h2]
      exact_mod_cast this
    have : m = 0 := by omega
    rw [this] at h1
    norm_num at h1
  · -- Show that the sum equals the final value modulo 1.
    simp
    all_goals
      norm_num
      all_goals
        norm_num