import Mathlib

theorem number_theory_298599 (b c : ℤ) (M : Set ℤ) (hM : M = {x^2 + b * x * y + c * y^2 | (x : ℤ) (y : ℤ)}) :
    ∀ m ∈ M, ∀ n ∈ M, m * n ∈ M := by 
  intro m hm n hn 
  rw [hM] at *
  rcases hm with ⟨x1, y1, rfl⟩ 
  rcases hn with ⟨x2, y2, rfl⟩ 
  use x1 * x2 - c * y1 * y2
  use x1 * y2 + x2 * y1 + b * y1 * y2
  ring_nf