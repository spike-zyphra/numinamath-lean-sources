import Mathlib

theorem number_theory_253290 : {n | ∃ k : ℕ, n = 500 + k * 1000 ∧ k ∈ Finset.Icc 1 7} = {500 + 1 * 1000, 500 + 2 * 1000, 500 + 3 * 1000, 500 + 4 * 1000, 500 + 5 * 1000, 500 + 6 * 1000, 500 + 7 * 1000} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First, prove LHS to RHS - that is, given there exists k in [1,7], with n = 500 + 1000k, prove n in the explicit set.
    rintro ⟨k, hn, ⟨hk1, hk7⟩⟩
    have h1 : k ≤ 7 := by omega
    have h2 : k ≥ 1 := by omega
    interval_cases k <;> norm_num [hn] at *
  · -- Now prove RHS to LHS - that is, given n in the explicit set (each element), find a k such that n = 500 + 1000k, with k in Finset.Icc 1 7
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- Show exists k.
      refine ⟨1, by norm_num, by norm_num⟩
    · -- Show exists k.
      refine ⟨2, by norm_num, by norm_num⟩
    · -- Show exists k.
      refine ⟨3, by norm_num, by norm_num⟩
    · -- Show exists k.
      refine ⟨4, by norm_num, by norm_num⟩
    · -- Show exists k.
      refine ⟨5, by norm_num, by norm_num⟩
    · -- Show exists k.
      refine ⟨6, by norm_num, by norm_num⟩
    · -- Show exists k.
      refine ⟨7, by norm_num, by norm_num⟩