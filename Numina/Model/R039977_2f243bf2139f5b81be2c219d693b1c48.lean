import Mathlib

theorem algebra_291369 :
  {x : ℝ | (x - 2)^4 + (x - 1)^4 = (17 / 4) * (x - 2)^2 * (x - 1)^2} = 
  {0, 3, 5/3, 4/3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
            Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume the original equation holds
    intro h
    have h1 : (x - 2)^4 + (x - 1)^4 - (17 / 4) * (x - 2)^2 * (x - 1)^2 = 0 := by 
      linarith 
    have h2 : (x - 0) * (x - 3) * (x - 5/3) * (x - 4/3) = 0 := by 
      nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 3), 
                sq_nonneg (x - 5/3), sq_nonneg (x - 4/3), 
                sq_nonneg ((x - 2) - (x - 1)), 
                sq_nonneg ((x - 1) + (x - 2)), 
                sq_nonneg ((x) - 3/2)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · cases' (mul_eq_zero.mp h3) with h5 h6
      · cases' (mul_eq_zero.mp h5) with h7 h8
        · -- case h7 : x - 0 =0
          have hx : x = 0 := by
            linarith
          simp [hx]
        · -- case h8 : x - 3 =0
          have hx : x = 3 := by
            linarith
          simp [hx]
      · -- case h6 : x - 5/3 =0
        have hx : x = 5/3 := by
          linarith
        simp [hx]
    · -- case h4 : x - 4/3 =0
      have hx : x = 4/3 := by
        linarith
      simp [hx]
  · -- Assume x is in the set
    rintro (rfl | rfl | rfl | rfl)
    · -- x = 0
      norm_num
    · -- x = 3
      norm_num
    · -- x = 5/3
      norm_num
    · -- x = 4/3
      norm_num