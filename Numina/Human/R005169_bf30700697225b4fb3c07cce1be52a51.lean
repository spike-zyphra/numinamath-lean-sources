import Mathlib

open Real
open scoped BigOperators

/- 
Problem:
Does there exist a hexagon (not necessarily convex) with side lengths 1, 2, 3, 4, 5, 6 (not necessarily in this order) that can be tiled with a) 31 b) 32 equilateral triangles with side length 1 ?
-/
theorem geometry_605970 :
    ∃ a : Fin 6 → ℝ,
    (∀ i, a i = 1 ∨ a i = 2 ∨ a i = 3 ∨ a i = 4 ∨ a i = 5 ∨ a i = 6) ∧
    ((∑ i, a i) = 31 ∨ (∑ i, a i) = 32) := by
  
  -- Define a hexagon with side lengths: five sides of length 6 and one side of length 1
  use fun i => if i.val = 5 then 1 else 6
  constructor
  ·
    -- Prove that each side length is one of the required values (1,2,3,4,5,6)
    intro i
    have h : i.val < 6 := i.is_lt
    
    -- Enumerate all possible values for i.val (0 to 5)
    have h₁ : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
      omega
    
    -- Case analysis for each possible value of i.val
    rcases h₁ with (h₁ | h₁ | h₁ | h₁ | h₁ | h₁) <;>
    simp [h₁]
  ·
    -- Prove that the sum of the side lengths is 31
    have h : (∑ i : Fin 6, (if i.val = 5 then (1 : ℝ) else 6)) = 31 := by
      simp [Fin.sum_univ_succ]
      ring
    exact Or.inl h

