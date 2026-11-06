import Mathlib

theorem number_theory_604122 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ IsSquare (400 * 10000 + n)} = {4001, 8004} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume h : n ∈ {n | n ∈ [1000, 9999] ∧ IsSquare (4000000 + n)}
    rintro ⟨⟨hn1, hn2⟩, h⟩
    rcases h with ⟨r, hr⟩
    have hr' : 400 * 10000 + n = r ^ 2 := by
      linarith [hr]
    have h1 : r ≤ 2002 := by
      nlinarith
    have h2 : r ≥ 2001 := by
      nlinarith
    have : r = 2001 ∨ r = 2002 := by
      omega
    rcases this with (hr1 | hr2)
    · -- r = 2001
      have : n = 4001 := by
        nlinarith [hr1, hr']
      tauto
    · -- r = 2002
      have : n = 8004 := by
        nlinarith [hr2, hr']
      tauto
  · -- Show n in the left side set.
    rintro (hn1 | hn2)
    · -- n = 4001.
      constructor
      · -- Show n ∈ [1000, 9999].
        rw [hn1]
        exact ⟨by norm_num, by norm_num⟩
      · -- Show 4004001 is a perfect square.
        rw [hn1]
        native_decide
    · -- n = 8004.
      constructor
      · -- Show 8004 ∈ [1000, 9999].
        rw [hn2]
        exact ⟨by norm_num, by norm_num⟩
      · -- Show 4008004 is a perfect square.
        rw [hn2]
        native_decide