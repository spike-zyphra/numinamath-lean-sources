import Mathlib

theorem algebra_291179 :
  {(n, x) : ℕ × ℤ | n > 0 ∧ n ≥ 4 ∧ (n + 5) * (x + 6) = n * x + 792 ∧ (n - 4) * (x + 4) = n * x - 388} =
  {(27, 120)} := by
  ext ⟨n, x⟩
  simp
  constructor
  · -- Assume (n, x) is in left side, prove (n, x) = (27, 120)
    rintro ⟨hn1, hn2, h1, h2⟩
    have eq1 : (6 : ℤ) * (n : ℤ) + 5 * x = 762 := by
      nlinarith
    have eq2 : (n : ℤ) - x = -93 := by
      have h3 : (n : ℤ) ≥ 4 := by
        omega
      nlinarith
    have hx : (x : ℤ) = 120 := by
      omega
    have hn : (n : ℤ) = 27 := by
      omega
    have hhn : n = 27 := by
      omega
    have hhx : x = 120 := by
      omega
    simp [hhn, hhx]
  · -- Assume (n, x) = (27, 120) prove inside left side
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num  -- n > 0
    constructor
    · norm_num -- n ≥ 4
    constructor
    · norm_num
    · norm_num