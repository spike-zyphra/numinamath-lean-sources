import Mathlib

theorem number_theory_70442 : {x : ℤ | (12 * x - 1) * (6 * x - 1) * (4 * x - 1) * (3 * x - 1) = 330}.encard = 1 := by 
  have h1 : {x : ℤ | (12 * x - 1) * (6 * x - 1) * (4 * x - 1) * (3 * x - 1) = 330} = {1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- First prove {x}
      intro h
      have eq : (12 * x - 1) * (6 * x - 1) * (4 * x - 1) * (3 * x - 1) = 330 := h
      have h2 : x ≤ 6 := by
        by_contra h
        push_neg at h
        have h3 : (12 * x - 1) * (6 * x - 1) * (4 * x - 1) * (3 * x - 1) > 330 := by
          have h4 : x ≥ 7 := by omega
          nlinarith [sq_nonneg (x - 1), sq_nonneg (x * (x - 1) * (x - 2)), sq_nonneg ((12 * x - 1) - 85), sq_nonneg ((6 * x - 1) - 35), sq_nonneg ((4 * x - 1) - 23), sq_nonneg ((3 * x - 1) - 17), h4, mul_nonneg (show 0 ≤ x - 1 by nlinarith) (show 0 ≤ (x - 2) by nlinarith)]
        nlinarith
      have h3 : x ≥ -3 := by 
        by_contra h 
        push_neg at h 
        have h4 : (12 * x - 1) * (6 * x - 1) * (4 * x - 1) * (3 * x - 1) > 330 := by
          have h5 : x ≤ -4 := by omega
          nlinarith [sq_nonneg (x + 4), sq_nonneg (x * (x + 1) * (x + 2)), sq_nonneg ((12 * x - 1) + 47), sq_nonneg ((6 * x - 1) + 23), sq_nonneg ((4 * x - 1) + 15), sq_nonneg ((3 * x - 1) + 11), mul_nonneg (show 0 ≤ (-x) - 1 by nlinarith) (show 0 ≤ (-x) - 3 by nlinarith)]
        nlinarith
      interval_cases x <;> norm_num at eq <;> tauto
    · -- Backward
      intro h
      rw [h]
      norm_num
  rw [h1]
  simp [Set.encard_singleton]