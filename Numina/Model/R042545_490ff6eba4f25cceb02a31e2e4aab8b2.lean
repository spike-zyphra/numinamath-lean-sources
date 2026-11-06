import Mathlib

theorem algebra_250836 :
    {x : ℝ | 6 * x ^ 5 - x ^ 4 - 43 * x ^ 3 + 43 * x ^ 2 + x - 6 = 0} = 
    {1, -3, -1/3, 2, 1/2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
          Set.union_insert, Set.union_singleton]
  constructor
  · -- Forward direction: if x satisfies the equation, then x ∈ {1, -3, -1/3, 2, 1/2}
    intro h_eq
    have h_eq2 : (x - 1) * (x + 3) * (x + 1/3) * (x - 2) * (x - 1/2) = 0 := by
      ring_nf
      linarith
    cases' (mul_eq_zero.mp h_eq2) with h1 h2
    cases' (mul_eq_zero.mp h1) with h1 h3
    cases' (mul_eq_zero.mp h1) with h1 h4
    cases' (mul_eq_zero.mp h1) with h1 h5
    · -- Case $x - 1 = 0: x = 1$.
      have hx : x = 1 := by linarith
      simp [hx]
    · -- Case $x + 3 = 0: x = -3$.
      have hx : x = -3 := by linarith
      simp [hx]
    · -- Case $x + 1/3 = 0: x = -1/3$.
      have hx : x = -1/3 := by linarith
      simp [hx]
    · -- Case $x - 2 = 0: x = 2$.
      have hx : x = 2 := by linarith
      simp [hx]
    · -- Case $x - 1/2 = 0: x = 1/2$.
      have hx : x = 1/2 := by linarith
      simp [hx]
  · -- Backward implication: if x ∈ {1, ±3, -1/3, 1/2}, then it is a solution.
    rintro (rfl | rfl | rfl | rfl | rfl)
    · -- x = 1.
      norm_num
    · -- x = -3.
      norm_num
    · -- x = -1/3.
      norm_num
    · -- x = 2.
      norm_num
    · -- x = 1/2.
      norm_num