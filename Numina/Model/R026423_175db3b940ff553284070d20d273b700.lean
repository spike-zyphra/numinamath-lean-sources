import Mathlib

theorem algebra_193738 :
    Set.Infinite {(x, y) : ℝ × ℝ | 2 * x ^ 2 - x * y - y ^ 2 - x - 2 * y - 1 = 0 ∧ 3 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x + y = 0} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => ( (↑t : ℝ) , (↑t : ℝ) -1))
  · -- Show f is injective
    intro t1 t2 h
    simp [Prod.ext_iff] at h
    linarith
  · -- Show that all elements of f(t) are in the set.
    intro t
    simp only [Set.mem_setOf_eq]
    constructor
    · -- Show 2 * x ^ 2 - x * y - y ^ 2 - x - 2 * y - 1 = 0 
      norm_num
      <;> ring_nf 
    · -- Show 3 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x + y = 0 
      norm_num
      <;> ring_nf