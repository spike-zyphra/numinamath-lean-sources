import Mathlib

theorem number_theory_98807 {n : ℕ} (hn : ∀ d, d ∣ n → ¬ ∃ k, k^2 = d) :
    ¬∃ x y : ℕ, x > 0 ∧ y > 0 ∧ Nat.Coprime x y ∧ (x + y)^3 ∣ x^n + y^n := by
  have h1 := hn 1 (by simp)
  have h2 : ∃ k, k ^ 2 = 1 := by
    use 1
    all_goals norm_num
  exfalso
  have h2' := h1 h2
  all_goals tauto