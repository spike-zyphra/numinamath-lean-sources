import Mathlib

theorem number_theory_176949 :
    ∀ n : ℤ, Even n → (∃ a b, a + b = n ∧ ∃ m, m^2 = a * b) ∨
    (∃ a b, a - b = n ∧ ∃ m, m^2 = a * b ∨ m^2 = -a * b) := by 
  intro n hn
  have h1 : n % 2 = 0 := by 
    obtain ⟨k, hk⟩ := hn
    omega 
  obtain ⟨k, hk⟩ := hn
  rw [show n = 2 * k by linarith [hk]]
  left 
  use k, k 
  constructor 
  · -- Show that k + k = 2 * k 
    all_goals ring
  · -- Show the existence of a perfect square 
    use k
    all_goals ring