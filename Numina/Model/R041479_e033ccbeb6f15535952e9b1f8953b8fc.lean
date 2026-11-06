import Mathlib

theorem number_theory_286745 :
  {(r, e) : ℕ × ℕ | r > 0 ∧ e > 0 ∧ r * 200 - e * 16 = 440 ∧ e < 10 * r ∧ e > 9 * r} =
  {(9, 85)} := by
  ext ⟨r, e⟩
  simp [-Nat.mul_sub]
  constructor
  · -- Assume (r, e) in the set, prove (9, 85).
    rintro ⟨hr, he, heq, he1, he2⟩
    have eq1 : r * 200 = e * 16 + 440 := by
      omega
    have h1 : r ≤ 10 := by
      omega
    have h2 : r ≥ 8 := by
      omega
    interval_cases r <;> omega
  · -- Assume (9, 85). Prove (r, e) in the set.
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num -- r > 0
    constructor
    · norm_num -- e > 0
    constructor
    · norm_num -- Check equation
    constructor
    · norm_num -- Check e < 10 * r
    · norm_num -- Check e > 9 * r