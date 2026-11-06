import Mathlib

theorem algebra_188690 (a d : ℚ) (h : d ≠ 0) :
    ∃ f : ℕ → ℕ, ∀ n, ∃ m, f n = a + m * d ∧
      ∃ r : ℚ, ∀ n, f (n + 1) / f n = r := by 
  use (λ _ => (0 : ℕ))
  intro n 
  use (-a / d)
  constructor 
  · -- Show that f n = a + m * d
    simp 
    <;> field_simp [h]
    <;> ring
  · -- Show that there exists a rational r such that for all n, f (n + 1) / f n = r
    use (0 : ℚ)
    intro n 
    simp 
    all_goals norm_num