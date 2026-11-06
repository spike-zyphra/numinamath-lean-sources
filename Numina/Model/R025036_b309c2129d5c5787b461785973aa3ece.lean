import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_153858 :
  {z : ℝ | ∃ x y : ℝ, z = x^2 + (x * y + 1)^2} = {z | 0 < z} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First direction: if z in the left side, then z in the right side
    rintro ⟨x, y, hz⟩
    have h1 : x ^ 2 ≥ 0 := sq_nonneg x
    have h2 : (x * y + 1) ^ 2 ≥ 0 := sq_nonneg (x * y + 1)
    have h4 : z > 0 := by
      nlinarith [sq_nonneg (x * y + 1), sq_nonneg x, sq_nonneg (y), sq_nonneg (x * y), sq_nonneg (x - y),
        sq_nonneg (x + y)]
    linarith
  · -- Second direction: if z in the right side, then z in the left side
    intro hz
    have h1 : z > 0 := hz
    have h2 : Real.sqrt z > 0 := by
      apply Real.sqrt_pos.2 
      linarith
    have h3 : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (by linarith)
    use Real.sqrt z
    use -1 / Real.sqrt z
    field_simp [h2]
    <;> nlinarith [ Real.sqrt_nonneg z, h3, sq_nonneg (Real.sqrt z ^ 2 - z), sq_nonneg (Real.sqrt z ) ]