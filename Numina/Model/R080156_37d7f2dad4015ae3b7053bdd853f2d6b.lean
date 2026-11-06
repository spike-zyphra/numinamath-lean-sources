import Mathlib

theorem algebra_12999 : {z : ℂ | z ^ 2 - (2 + 2 * Complex.I) * z + 10 * Complex.I = 0} = {3 - Complex.I, -1 + 3 * Complex.I} := by 
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Forward: if z is a root, then z ∈ {3 - i, -1 + 3i}
    intro h
    have h1 : z^2 - (2 + 2 * Complex.I) * z + 10 * Complex.I = 0 := h
    have eq1 : z^2 - (2 + 2 * Complex.I) * z + 10 * Complex.I = (z - (3 - Complex.I)) * (z - (-1 + 3 * Complex.I)) := by
      ring_nf
      simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
      all_goals
        ring_nf
        <;> norm_num
        <;> ring
    rw [eq1] at h1
    cases (mul_eq_zero.1 h1) with
    | inl h2 =>
      have h3 : z = 3 - Complex.I := by
        exact eq_of_sub_eq_zero h2
      left
      exact h3
    | inr h2 =>
      have h4 : z = -1 + 3 * Complex.I := by
        exact eq_of_sub_eq_zero h2
      right
      exact h4
  · -- Backward: if z ∈ {3 - i, -1 + 3i}, then z is a root
    rintro (h | h)
    · -- Case z =3 - i
      rw [h]
      norm_num [pow_two, Complex.ext_iff, Complex.I_mul_I]
    · -- Case z =-1 + 3i
      rw [h]
      norm_num [pow_two, Complex.ext_iff, Complex.I_mul_I]