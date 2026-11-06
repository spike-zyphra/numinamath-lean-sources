import Mathlib

theorem number_theory_16345 :
  let a (n : ℕ) := 3 * n + 2
  let b (n : ℕ) := 7 * n + 3
  IsGreatest {x | ∃ m n, x = a m ∧ x = b n ∧ x < 500} 479 := by
  intro a b
  constructor
  · -- Show that 479 is in the set.
    use 159, 68
    simp [a, b]
  · -- Show that no greater element is in the set.
    intro x hx
    rcases hx with ⟨m, n, h1, h2, h3⟩
    simp [a, b] at h1 h2
    omega