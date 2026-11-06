import Mathlib

theorem algebra_1184 (f : ℝ → ℝ) (hf : f = fun x => 5 * x ^ 2 - 20 * x + 1357) :
IsLeast (Set.image f {x | ∃ x : ℝ, x ∈ Set.univ}) 1337 := by
  have h1 : ∀ x, f x = 5 * (x - 2) ^ 2 + 1337 := by
    intro x
    rw [hf]
    calc 
      5 * x ^ 2 - 20 * x + 1357 = 5 * (x ^ 2 - 4 * x) + 1357 := by ring
      _ = 5 * ((x - 2) ^ 2 - 4) + 1357 := by ring
      _ = 5 * (x - 2) ^ 2 - 20 + 1357 := by ring
      _ = 5 * (x - 2) ^ 2 + 1337 := by ring
  constructor
  · -- Show that there exists some real number x such that f(x) = 1337
    use 2
    simp [h1]
  · -- Show that 1337 is indeed the smallest value
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1 x] at hx
    have h2 : 5 * (x - 2) ^ 2 + 1337 ≥ 1337 := by
      linarith [show 5 * (x - 2) ^ 2 ≥ 0 by positivity]
    linarith
  all_goals
  try linarith
  all_goals
  try tauto
  all_goals
  try nlinarith