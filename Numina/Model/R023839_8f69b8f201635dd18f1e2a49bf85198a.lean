import Mathlib.Tactic

theorem algebra_133813 {α : Type*} {f : α → α → α}
    (h : ∀ x y, f (f x y) x = y) : ∀ x y, f x (f y x) = y := by
  intro x y
  have h1 : f (f y x) y = x := by
    specialize h y x
    simpa using h
  have h2 : f (f (f y x) y) (f y x) = y := by 
    specialize h (f y x) y
    simpa using h
  rw [show f (f y x) y = x by exact h1] at h2
  simpa using h2