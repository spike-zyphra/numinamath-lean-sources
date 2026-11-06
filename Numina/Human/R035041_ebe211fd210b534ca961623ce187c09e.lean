import Mathlib

/- A polynomial with integer coefficients is of the form
\[3x^3 + a_2 x^2 + a_1 x - 6 = 0.\]Enter all the possible integer roots of this polynomial, separated by commas. -/
theorem algebra_21671 : {x : ℤ | ∃ a1 a2 : ℤ, 3 * x ^ 3 + a2 * x ^ 2 + a1 * x - 6 = 0} = {6, 3, 2, 1, -1, -2, -3, -6} := by
  ext x
  constructor
  · -- if $x$ is a root of the polynomial, then $x \in \{-6, -3, -2, -1, 1, 2, 3, 6\}$
    intro hx
    rcases hx with ⟨a1, a2, h⟩
    simp only [Int.reduceNeg, Set.mem_insert_iff, Set.mem_singleton_iff]
    -- $x \neq 0$
    have xne : x ≠ 0 := by
      by_contra contra
      rw [contra] at h
      norm_num at h
    apply eq_of_sub_eq_zero at h
    -- $x \mid 6$
    have xdvd : x ∣ 3 * x ^ 3 + a2 * x ^ 2 + a1 * x := by
      use 3 * x ^ 2 + a2 * x + a1
      ring
    rw [h] at xdvd
    -- so $x = -6, -3, -2, -1, 1, 2, 3, 6$
    have xle : x ≤ 6 := by
      apply Int.le_of_dvd (by norm_num) xdvd
    have xge : -6 ≤ x := by
      by_contra contra
      rw [not_le] at contra
      have negxdvd : -x ∣ 6 := by
        exact Int.neg_dvd.mpr xdvd
      apply Int.le_of_dvd (by norm_num) at negxdvd
      linarith
    interval_cases x
    simp
    norm_num at xdvd
    norm_num at xdvd
    simp
    simp
    simp
    norm_num at xdvd
    simp
    simp
    simp
    norm_num at xdvd
    norm_num at xdvd
    simp
  · -- if $x \in \{-6, -3, -2, -1, 1, 2, 3, 6\}$, then $x$ is a root of the polynomial
    intro hx
    simp only [Int.reduceNeg, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- $x = 6$
      use -107
      use 0
      norm_num
    · -- $x = 3$
      use -25
      use 0
      norm_num
    · -- $x = 2$
      use -9
      use 0
      norm_num
    · -- $x = 1$
      use 3
      use 0
      norm_num
    · -- $x = -1$
      use -9
      use 0
      norm_num
    · -- $x = -2$
      use -15
      use 0
      norm_num
    · -- $x = -3$
      use -29
      use 0
      norm_num
    · -- $x = -6$
      use -109
      use 0
      norm_num