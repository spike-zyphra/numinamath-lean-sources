import Mathlib

theorem number_theory_15166 : (0 ≤ n ∧ n < 19 ∧ -200 ≡ n [ZMOD 19]) ↔ n = 9 := by 
  constructor 
  · -- Assume (0 ≤ n ∧ n < 19 ∧ -200 ≡ n [ZMOD 19]), prove n = 9
    rintro ⟨h0, h1, h2⟩
    norm_num [Int.ModEq] at h2
    omega
  · -- Assume n = 9, prove (0 ≤ n ∧ n < 19 ∧ -200 ≡ n [ZMOD 19])
    intro h
    rw [h]
    constructor 
    · norm_num -- 0 ≤ 9
    constructor 
    · norm_num -- 9 < 19
    · -- Check that -200 ≡ 9 [ZMOD 19]
      norm_num [Int.ModEq]