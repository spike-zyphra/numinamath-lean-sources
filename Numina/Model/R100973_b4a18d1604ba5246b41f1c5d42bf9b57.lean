import Mathlib

def f (x y : ℝ) := 4 * x - 3 * y + x * y

theorem algebra_97778 : {y | f 3 y = 12}.Infinite := by 
  have h : ∀ y : ℝ, f 3 y = 12 := by
    intro y
    dsimp [f]
    ring
  have : {y : ℝ | f 3 y = 12} = Set.univ := by
    ext y
    simp [h]
  rw [this]
  apply Set.infinite_of_injective_forall_mem (f := (λ (n : ℕ) => (n : ℝ)))
  · -- Show that the function is injective
    intro n m h
    simpa using h
  · -- Show that all elements of the image are in the universal set
    intro n
    trivial