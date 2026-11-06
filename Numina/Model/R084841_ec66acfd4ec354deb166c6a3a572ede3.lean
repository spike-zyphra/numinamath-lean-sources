import Mathlib

theorem algebra_116077 {u : ℕ → ℤ} (hu : ∀ n, u n = n ^ 2) :
    ∀ n, u (n + 1) - u n = 2 * n + 1 := by 
  intro n
  have h1 : u (n + 1) = (n + 1) ^ 2 := by 
    specialize hu (n + 1)
    simpa using hu
  have h2 : u n = n ^ 2 := by
    specialize hu n 
    simpa using hu 
  rw [h1, h2]
  simp [add_sq]
  <;> ring_nf 
  <;> simp [add_sq]
  all_goals ring