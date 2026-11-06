import Mathlib

theorem algebra_93812 (f g : ℝ → ℝ) 
    (hf : f = λx ↦ x) 
    (hg : g = λx ↦ x - 2) : 
    {x : ℝ | f x = g x} = ∅  := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  simp [hf, hg]
  all_goals
    intro h
    linarith