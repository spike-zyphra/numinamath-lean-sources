import Mathlib

lemma lemma1 {x y: ℤ}: 3 * y ^ 2 + 3 * x * y + x + y = (x + y) * (3 * y + 1) := by
  ring

/-Find integers x y such that 3 * y ^ 2 + 3 * x * y + x + y = 2019-/

theorem algebra_196962: {(x, y): ℤ × ℤ | 3 * y ^ 2 + 3 * x * y + x + y = 2019} =
  {(-221, 224), (2019, 0)} := by

  ext ⟨x, y⟩
  constructor

  -- the forward direction
  .
    simp only [Set.mem_setOf_eq]
    intro h
    rw [lemma1] at h
    simp
    have d: (3 * y + 1).natAbs ∈ Nat.divisors 2019 := by
      simp
      replace h: ((x + y) * (3 * y + 1)).natAbs = 2019 := by
        rw [h]
        simp
      rw [Int.natAbs_mul] at h
      rw [← h]
      simp
    rw [show Nat.divisors 2019 = {1, 3, 673, 2019} by native_decide] at d
    simp at d
    zify at d
    by_cases l: 0 ≤ y

    -- case 0 ≤ y
    .
      rw [show |3 * y + 1| = 3 * y + 1 by apply abs_of_nonneg; omega] at d
      rcases d with d | d | d | d
      .
        simp at d
        simp [d] at h
        omega
      .
        replace d: 1 = 3 * (1 - y) := by omega
        have o: 3 ∣ 1 := by
          zify
          rw [d]
          simp
        norm_num at o
      .
        replace d: y = 224 := by omega
        simp [d] at h
        replace h: x = -221 := by omega
        omega
      .
        replace d: 3 * y = 2018 := by omega
        have o: 3 ∣ 2018 := by
          zify
          rw [← d]
          simp
        norm_num at o

    -- case y < 0
    .
      simp at l
      rw [show |3 * y + 1| = -(3 * y + 1) by apply abs_of_neg; omega] at d
      rcases d with d | d | d | d
      .
        replace d: 3 * y = -2 := by omega
        have o: 3 ∣ -2 := by
          rw [← d]
          simp
        norm_num at o
      .
        replace d: 3 * (1 - y) = 1 := by omega
        have o: 3 ∣ 1 := by
          zify
          rw [← d]
          simp
        norm_num at o
      .
        replace d: 3 * y = -674 := by omega
        have o: 3 ∣ -674 := by
          rw [← d]
          simp
        norm_num at o
      .
        replace d: 3 * y = -2018 := by omega
        have o: 3 ∣ -2018 := by
          rw [← d]
          simp
        norm_num at o


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
    .
      simp [h]