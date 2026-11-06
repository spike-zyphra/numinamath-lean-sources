import Mathlib

theorem number_theory_39671 (n : ℤ) :
    (∃ k, k ∈ Finset.Icc 1000 9999 ∧ k = 12 * n ^ 2 + 12 * n + 11 ∧
      ∃ d, d ∈ Finset.Icc 1000 9999 ∧ d = k ∧ d % 1111 = 0) ↔
    n = 21 ∨ n = -22 := by 
  constructor
  · -- Assume the existence statement, prove n = 21 ∨ n = -22.
    rintro ⟨k, hk1, hk2, d, hd1, hd2, hd3⟩ 
    rw [Finset.mem_Icc] at hk1 hd1
    have hk3 : k % 1111 = 0 := by 
      have h1 : d % 1111 = 0 := hd3
      have h2 : d = k := hd2
      rw [h2] at h1
      exact h1
    rw [hk2] at hk3
    rcases hk1 with ⟨hk1l, hk1u⟩
    rw [hk2] at hk1l
    rw [hk2] at hk1u
    have h1 : n ≥ -29 := by
      nlinarith [sq_nonneg (n + 22), sq_nonneg (n - 21)]
    have h2 : n ≤ 28 := by 
      nlinarith [sq_nonneg (n + 22), sq_nonneg (n - 21)]
    interval_cases n <;> norm_num [hk2] at *
    <;> omega 
  · -- Assume n = 21 ∨ n = -22, prove the existence statement.
    rintro (hn | hn)
    · -- n = 21
      rw [hn]
      use 5555
      constructor
      · -- Show k ∈ [1000, 9999]
        norm_num 
      constructor
      · -- Show k = 12n^2 + 12n + 11 
        norm_num
      · -- Show existence of d
        use 5555
        constructor
        · -- Show d ∈ [1000, 9999]
          norm_num
        constructor
        · -- Show d = k
          rfl
        · -- Show 5555 % 1111 = 0
          norm_num
    · -- n = -22
      rw [hn]
      use 5555
      constructor 
      · -- Show k ∈ [1000, 9999]
        norm_num 
      constructor
      · -- Show k = 12n^2 + 12n + 11 
        norm_num
      · -- Show existence of d
        use 5555
        constructor
        · -- Show d ∈ [1000, 9999]
          norm_num
        constructor
        · -- Show d = k
          rfl
        · -- Show 5555 % 1111 = 0
          norm_num