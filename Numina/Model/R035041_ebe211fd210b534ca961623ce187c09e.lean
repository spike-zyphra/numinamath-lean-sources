import Mathlib

theorem algebra_21671 : {x : ℤ | ∃ a1 a2 : ℤ, 3 * x ^ 3 + a2 * x ^ 2 + a1 * x - 6 = 0} = {6, 3, 2, 1, -1, -2, -3, -6} := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor 
  · -- Assume that x is a root: (∃ a1 a2: ℤ, 3x^3 + a2x^2 + a1x - 6 = 0) then (x ∈ {6, 3, 2, 1, -1, -2, -3, -6})
    rintro ⟨a1, a2, h⟩
    have h1 : x ∣ 6 := by
      use (3 * x ^ 2 + a2 * x + a1)
      linarith
    have h2 : x ≤ 6 := by 
      apply Int.le_of_dvd (by norm_num) h1
    have h3 : x ≥ -6 := by 
      have h4 : (-x) ∣ 6 := by
        exact Int.neg_dvd.2 h1
      have h5 : -x ≤ 6 := by 
        apply Int.le_of_dvd (by norm_num) h4
      omega 
    interval_cases x <;> norm_num at h1 h <;> tauto
  · -- Assume x ∈ {6, 3, 2, 1, -1, -2, -3, -6}, prove it's a root 
    rintro (h | h | h | h | h | h | h | h)
    · -- x = 6 
      rw [h] 
      use -107, 0 
      norm_num 
    · -- x = 3 
      rw [h] 
      use -25, 0 
      norm_num 
    · -- x = 2 
      rw [h] 
      use -9, 0 
      norm_num 
    · -- x = 1 
      rw [h] 
      use 0, 3 
      norm_num 
    · -- x = -1 
      rw [h] 
      use 0, 9 
      norm_num 
    · -- x = -2 
      rw [h] 
      use -15, 0 
      norm_num 
    · -- x = -3 
      rw [h] 
      use 1, 10 
      norm_num 
    · -- x = -6 
      rw [h] 
      use -109, 0 
      norm_num