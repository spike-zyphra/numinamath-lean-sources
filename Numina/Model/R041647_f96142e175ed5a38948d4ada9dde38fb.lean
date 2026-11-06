import Mathlib

theorem algebra_326513 :
    {(x, y) : ℝ × ℝ | 2 * x ^ 2 - x * y - y ^ 2 - x - 2 * y - 1 = 0 ∧
      3 * x ^ 2 - 4 * x * y + y ^ 2 - 3 * x + y = 0}.Infinite := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => ( ( (↑t : ℝ ) + 1 ), ( ↑t : ℝ ) ) )
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    linarith
  · -- Show that for all n, f n is in the set
    intro n
    simp [Prod.ext_iff]
    <;> ring_nf <;> norm_num