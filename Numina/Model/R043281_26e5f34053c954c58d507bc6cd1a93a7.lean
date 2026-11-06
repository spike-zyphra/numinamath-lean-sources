import Mathlib

theorem number_Theory_53170: {(x, y, z, b): ℤ × ℤ × ℤ × ℤ | 1 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
  x < b ∧ y < b ∧ z < b ∧ 2 ≤ b ∧ x * b ^ 2 + y * b + z = 1987 ∧ x + y + z = 1 + 9 + 8 + 7}
  = {(5, 9, 11, 19)} := by
  ext ⟨x, y, z, b⟩
  simp [-one_div]
  constructor
  · -- (x, y, z, b) is in the set ⇒ (5, 9, 11, 19)
    rintro ⟨hx, hy, hz, hx_lt_b, hy_lt_b, hz_lt_b, hb, heq1, heq2⟩
    have eq3 : (b - 1) * (x * (b + 1) + y) = 1962 := by
      nlinarith
    have h1 : (b - 1) ∣ 1962 := by
      use x * (b + 1) + y
      all_goals linarith
    have eq4 : b ≤ 1963 := by
      have h2 : (b - 1) ∣ 1962 := h1
      by_contra h
      push_neg at h
      have h3 : b - 1 > 1962 := by 
        omega
      have h5 : (b - 1) ∣ 1962 := h1
      have h5' : (b - 1) ≤ 1962 := by
        exact Int.le_of_dvd (by omega) h5
      all_goals linarith
    -- For $\mathrm{\text{x b ^ 2 + y b + z}} = 1987$
    -- First bound $b$ 
    have h2 : b ≤ 44 := by
      nlinarith [sq_nonneg (x * b ^ 2 - y * b - z), sq_nonneg (b ^ 2), sq_nonneg (b), sq_nonneg (x * b), sq_nonneg ((y)), sq_nonneg ((z)), sq_nonneg (b ^ 2)]
    interval_cases b <;> try { 
      omega 
    }
  · -- Backward direction: (5, 9, 11, 19) is in the set
    rintro ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num