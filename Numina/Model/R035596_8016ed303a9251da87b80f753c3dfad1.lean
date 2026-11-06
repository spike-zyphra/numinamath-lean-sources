import Mathlib

theorem number_theory_240895 :
    {n : ℕ | 0 < n ∧ ∃ m : ℕ, m ^ 3 = n ∧ n / 1000 = m} = {32768} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n in the set, with 0 < n and exists m, m^3 = n and n / 1000 = m
    rintro ⟨hn_pos, ⟨m, hm1, hm2⟩⟩
    have h1 : m ^ 3 = n := by linarith
    have h2 : n = m ^ 3 := by linarith
    rw [show n = m ^ 3 by linarith] at hm2
    have h3 : m ^ 3 = n := h1
    have h4 : m ≤ 100 := by
      by_contra h
      push_neg at h
      have h5 : m ^ 3 ≥ 1000 * m + 1000 := by
        nlinarith [sq_nonneg (m + 32 : ℤ), sq_nonneg (m - 32 : ℤ)]
      have h6 : m ^ 3 / 1000 = m := hm2
      have h7 : m ^ 3 ≥ 1000 * m := by
        omega
      have h7' : m ^ 3 < 1000 * (m + 1) := by
        omega
      nlinarith
    interval_cases m <;> norm_num at hm1 hm2 ⊢
    <;> omega
  · -- Assume n = 32768
    intro h
    rw [h]
    constructor
    · norm_num
    · -- Show there exists m such that m^3 = n and n / 1000 = m
      use 32
      all_goals norm_num