import Mathlib

theorem number_Theory_111409: {(x, y, z, b): ℤ × ℤ × ℤ × ℤ | 1 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
  x < b ∧ y < b ∧ z < b ∧ 2 ≤ b ∧ x * b ^ 2 + y * b + z = 1987 ∧ x + y + z = 1 + 9 + 8 + 7}
  = {(5, 9, 11, 19)} := by

  ext ⟨x, y, z, b⟩ 
  simp
  constructor
  · -- First, we show that if $(x, y, z, b)$ satisfies the conditions, then $(x, y, z, b) = (5, 9, 11, 19)$
    rintro ⟨hx1, hy0, hz0, hxd, hyd, hzd, hb2, heq, heq2⟩
    have h1 : b ≤ 44 := by 
      nlinarith [show x ≥ 1 by linarith, show b ≥ 2 by linarith, heq, hxd]
    have h2 : b > 8 := by 
      by_contra h
      push_neg at h
      interval_cases b <;> omega 
    interval_cases b <;> omega 
  · -- Now the reverse direction
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