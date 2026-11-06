import Mathlib

theorem number_theory_136633 : {(m, n) : ℤ × ℤ | m ^ 4 + 2 * n ^ 2 = 9 * m * n} = {(0, 0), (2, 1), (-2, -1), (2, 8), (-2, -8), (3, 9), (-3, -9)}:= by
  ext ⟨m, n⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume h ⊢.
    intro h
    have h1 : m ^ 4 + 2 * n ^ 2 = 9 * m * n := by
      linarith
    have h2 : m ≤ 4 := by
      nlinarith [sq_nonneg (m ^ 2), sq_nonneg (n - m ^ 2), sq_nonneg (n + m ^ 2), sq_nonneg (m ^ 2 - 3 ^ 2), sq_nonneg ((4 * n - 9 * m) ^ 2 - (m ^ 2 * 16))]
    have h3 : m ≥ -4 := by
      nlinarith [sq_nonneg (m ^ 2), sq_nonneg (n - m ^ 2), sq_nonneg (n + m ^ 2), sq_nonneg (m ^ 2 - 3 ^ 2), sq_nonneg ((4 * n - 9 * m) ^ 2 - (m ^ 2 * 16)), sq_nonneg ((m + 4) ^ 2)]
    have h6 : n ≤ 16 := by
      nlinarith [sq_nonneg (m ^ 2 - 4 ^ 2), sq_nonneg (n - m ^ 2), sq_nonneg (n + m * 4)]
    have h7 : n ≥ -16 := by
      nlinarith [sq_nonneg (m ^ 2 - 4 ^ 2), sq_nonneg (n + m * 4), sq_nonneg (n - m * 4)]
    interval_cases m <;> try { 
      omega
    }
    <;> try { 
      interval_cases n <;> norm_num at h1 ⊢ <;> tauto
    }
  · -- Assume h ⊢
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num