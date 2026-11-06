import Mathlib

theorem number_theory_186985 {n : ℕ} (hn : n > 0) (hnp : ∀ m, ¬ ∃ k, m^2 = k ∧ k ∣ n) :
    ¬∃ x y : ℕ, x > 0 ∧ y > 0 ∧ IsCoprime x y ∧ (x + y)^3 ∣ x^n + y^n := by
  have h1 := hnp 1
  have h4 : ¬ ∃ k, (1 : ℕ) ^ 2 = k ∧ k ∣ n := h1
  have h5 : ∃ k, (1 : ℕ) ^ 2 = k ∧ k ∣ n := by
    use 1
    all_goals norm_num
  contradiction