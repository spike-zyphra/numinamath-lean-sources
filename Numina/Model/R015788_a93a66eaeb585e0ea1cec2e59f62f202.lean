import Mathlib

def A : Set ℤ := {x | ∃ a b : ℤ, x = a^2 + 4 * a * b + b^2}

theorem number_theory_248677 (x y : ℤ) (hx : x ∈ A) (hy : y ∈ A) :
    x * y ∈ A := by 
  rcases hx with ⟨a, b, hx⟩
  rcases hy with ⟨c, d, hy⟩
  use a * c - b * d
  use a * d + b * c + 4 * b * d
  rw [hx, hy]
  ring