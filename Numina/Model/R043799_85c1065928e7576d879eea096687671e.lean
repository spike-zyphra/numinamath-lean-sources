import Mathlib


theorem algebra_10528 {f : ℝ → ℝ}  
  (hf : f 1 = 5 ∧ f 2 = 3 ∧ f 3 = 1) : 
  ∃ a b c d : ℝ, 
    (a, b) ∈ {(x, y) | y = f (f x)} ∧ 
    (c, d) ∈ {(x, y) | y = f (f x)} ∧ 
    a * b + c * d = 17 := by
  rcases hf with ⟨h1, h2, h3⟩
  use 2, 1, 3, 5
  constructor
  · -- Show that (2, 1) is in the graph of f(f(x))
    show 1 = f (f 2)
    rw [show f 2 = 3 by linarith]
    all_goals
      linarith [h3]
  constructor
  · -- Show that (3, 5) is in the graph of f(f(x))
    show 5 = f (f 3)
    rw [show f 3 = 1 by linarith]
    all_goals
      linarith [h1]
  all_goals
    norm_num