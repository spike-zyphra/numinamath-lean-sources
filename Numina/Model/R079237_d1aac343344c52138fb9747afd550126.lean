import Mathlib

def a (n : ℕ) := 1 + 3 * n
def b (n : ℕ) := 2 + 10 * n

theorem number_theory_290859 :
    IsLeast {x | ∃ m n, x = a m ∧ x = b n ∧ x > 2023} 2032 := by
  constructor
  · -- Show that 2032 is in the set
    use 677, 203
    simp [a, b]
    all_goals norm_num
  · -- Show that 2032 is the least element in the set
    intro x hx
    rcases hx with ⟨m, n, h1, h2, h3⟩
    simp [a, b] at h1 h2 h3
    omega