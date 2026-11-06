import Mathlib

/-
The problem describes a tree structure with 2010 nodes (cities), where each node represents a city and each edge represents a road. The goal is to determine the maximum number of nodes with a degree of at least 3.
-/  
theorem combinatorics_608689 
    (n : ℕ)
    (hn : n = 2010)
    (b : ℕ)
    (hb : b ≤ n)
    (h : 3 * b + (n - b) ≤ 2 * (n - 1)) : 
    b ≤ 1004 := by
  omega  

