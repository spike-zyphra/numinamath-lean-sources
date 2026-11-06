import Mathlib

theorem number_theory_25206 :
    Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 3 + y ^ 4 = z ^ 31} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ( (2^(31 * n) : ℤ) , (0 : ℤ) , (2^(3 * n) : ℤ) ) )
  · -- Show that the function is injective
    intro n m h
    simp [Prod.ext_iff] at h 
    linarith
  · -- Show that all the images under f are in the set
    intro n
    simp [Prod.ext_iff]
    all_goals ring_nf
    all_goals norm_num