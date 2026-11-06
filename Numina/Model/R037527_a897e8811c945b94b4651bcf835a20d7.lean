import Mathlib

theorem algebra_290176 {f : ℝ → ℝ} (α β : ℝ) (hα : α ≠ 0)
    (hβ : ∀ x, f (x + α) = f x + β) :
    ∃ g h, ∀ x, f x = g x + h x ∧ (∃ a b, g = fun x => a * x + b) ∧
    (∃ c, Function.Periodic h c) := by 
  use fun x => β / α * x + f 0
  use fun x => f x - (β / α * x + f 0)
  intro x
  constructor
  · -- Show that f(x) = g(x) + h(x)
    simp
  constructor
  · -- Show that g is linear
    use β / α, f 0
    all_goals funext
    <;> simp
  · -- Show that h is periodic
    refine' ⟨α, ?_⟩
    unfold Function.Periodic
    intro x
    simp [hβ]
    <;> field_simp [hα]
    <;> ring