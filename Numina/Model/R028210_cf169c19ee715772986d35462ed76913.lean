import Mathlib

theorem algebra_184160 {f : ℝ → ℝ} (hf : ∀ x, 0 ≠ x → 5 * x * f (1 / x) + 25 * f x = 15 / x ^ 2 ∧ 5 * x * f (1 / x) + f x = 3 * x ^ 3) :
    ∀ x, 0 ≠ x → f x = 5 / (8 * x ^ 2) - x ^ 3 / 8 := by
  intro x hx
  have h₁ := (hf x hx).1
  have h₂ := (hf x hx).2
  have eq1 : 24 * f x = 15 / x ^ 2 - 3 * x ^ 3 := by 
    linarith
  have eq2 : f x = (15 / x ^ 2 - 3 * x ^ 3) / 24 := by
    linarith
  rw [eq2]
  have eq3 : (15 / x ^ 2 - 3 * x ^ 3) / 24 = 5 / (8 * x ^ 2) - x ^ 3 / 8 := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  rw [eq3]
  all_goals field_simp
  <;> ring_nf <;> field_simp