import Mathlib

/-How many ordered pairs of integers (x,y) are there in total for which
x⋅y=1987 holds? -/

theorem number_theory_190556: {(x, y): ℤ × ℤ | x * y = 1987}.encard = 4 := by

  -- we directly compute the set
  have h_eq: {(x, y): ℤ × ℤ | x * y = 1987} = {(1, 1987), (1987, 1), (-1, -1987), (-1987, -1)} := by
    ext ⟨x, y⟩
    constructor
    -- the forward direction
    .
      intro h
      simp at h
      have l: (x * y).natAbs = 1987 := by rw [h]; simp
      rw [Int.natAbs_mul] at l
      have o: Nat.divisors 1987 = {1, 1987} := by
        native_decide
      have lx: x.natAbs ∈ Nat.divisors 1987 := by
        simp
        rw [← l]
        simp
      rw [o] at lx
      clear o
      simp at lx
      rcases lx with lx | lx
      .
        simp [lx] at l
        zify at lx l
        by_cases i: 0 ≤ x
        .
          rw [show |x| = x by apply abs_of_nonneg; linarith] at lx
          simp [lx] at h
          simp [lx, h]
        .
          rw [show |x| = -x by apply abs_of_neg; linarith] at lx
          replace lx: x = -1 := by omega
          simp [lx] at h
          replace h: y = -1987 := by omega
          simp [lx, h]
      .
        simp [lx] at l
        zify at lx l
        by_cases i: 0 ≤ x
        .
          rw [show |x| = x by apply abs_of_nonneg; linarith] at lx
          simp [lx] at h
          simp [lx, h]
        .
          rw [show |x| = -x by apply abs_of_neg; linarith] at lx
          replace lx: x = -1987 := by omega
          simp [lx] at h
          replace h: y = -1 := by omega
          simp [lx, h]

    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h | h
      .
        simp [h]
      .
        simp [h]
      .
        simp [h]
      .
        simp [h]


  -- then we count the cardinality of the set
  rw [h_eq]
  simp [Set.encard_insert_of_not_mem]
  norm_num