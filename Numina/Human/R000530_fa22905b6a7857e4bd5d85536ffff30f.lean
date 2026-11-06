import Mathlib

/-A math teacher requires Noelle to do one homework assignment for each of the first five homework points she wants to earn; for each of the next five homework points, she needs to do two homework assignments; and so on, so that to earn the $n^{\text{th}}$ homework point, she has to do $n\div5$ (rounded up) homework assignments. For example, when she has 11 points, it will take $12\div5=2.4\rightarrow3$ homework assignments to earn her $12^{\text{th}}$ point. What is the smallest number of homework assignments necessary to earn a total of 25 homework points?-/
theorem algebra_11985 {assignments : ℤ → ℤ} (h : ∀ n, assignments n = n / 5 + 1) :
∑ i ∈ Finset.range 25, assignments i = 75 := by
-- This is a straightforward computation
  simp only [h]; norm_num