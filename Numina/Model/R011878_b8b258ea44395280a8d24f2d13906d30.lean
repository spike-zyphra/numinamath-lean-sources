import Mathlib

theorem number_theory_155335 :
    {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 28 ∣ n ∧ ∃ k, n = (2 * k) ^ 2 + (2 * k + 2) ^ 2 + (2 * k + 4) ^ 2} = {1736, 3080, 4340, 6356, 8120} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, we show that if n is in the left side, it is in the right side.
    rintro ⟨⟨hn1, hn2⟩, hdiv, ⟨k, heq⟩⟩
    have h1 : n = 12 * k ^ 2 + 24 * k + 20 := by
      nlinarith
    have h4 : k ≤ 27 := by
      by_contra h
      push_neg at h
      have : k ≥ 28 := by omega
      nlinarith [h1, show n ≤ 9999 by linarith]
    have h5 : k ≥ 0 := by omega
    interval_cases k <;> norm_num [h1] at *
    <;> omega
  · -- Now prove the reverse: if n is in the right side, it is in the left side.
    rintro (rfl | rfl | rfl | rfl | rfl)
    · -- n = 1736
      constructor
      · -- Show n is in the range [1000, 9999]
        norm_num
      constructor
      · -- Show 28 divides n
        norm_num
      · -- Show there exists k such that n = (2*k)^2 + (2*k+2)^2 + (2*k+4)^2
        use 11
        all_goals norm_num
    · -- n = 3080
      constructor
      · -- Show n is in the range [1000, 9999]
        norm_num
      constructor
      · -- Show 28 divides n
        norm_num
      · -- Show there exists k such that n = (2*k)^2 + (2*k+2)^2 + (2*k+4)^2
        use 15
        all_goals norm_num
    · -- n = 4340
      constructor
      · -- Show n is in the range [1000, 9999]
        norm_num
      constructor
      · -- Show 28 divides n
        norm_num
      · -- Show there exists k such that n = (2*k)^2 + (2*k+2)^2 + (2*k+4)^2
        use 18
        all_goals norm_num
    · -- n = 6356
      constructor
      · -- Show n is in the range [1000, 9999]
        norm_num
      constructor
      · -- Show 28 divides n
        norm_num
      · -- Show there exists k such that n = (2*k)^2 + (2*k+2)^2 + (2*k+4)^2
        use 22
        all_goals norm_num
    · -- n = 8120
      constructor
      · -- Show n is in the range [1000, 9999]
        norm_num
      constructor
      · -- Show 28 divides n
        norm_num
      · -- Show there exists k such that n = (2*k)^2 + (2*k+2) ^ 2 + (2*k+4) ^ 2
        use 25
        all_goals norm_num