import Mathlib


open Int


theorem number_theory_6338 :
    (X^3 + X^2 + 10*X + 1 ≡ 0 [ZMOD 3^3]) ↔ X ≡ -10 [ZMOD 3^3] := by
  constructor
  · -- Assume (X^3 + X^2 + 10*X + 1 ≡ 0 [ZMOD 3^3]), prove (X ≡ -10 [ZMOD 3^3])
    intro h
    have h1 : (X ^ 3 + X ^ 2 + 10 * X + 1) % 27 = 0 := by
      norm_num [Int.ModEq] at h ⊢
      omega
    have h2 : X % 27 = 17 := by
      have h1' : (X ^ 3 + X ^ 2 + 10 * X + 1) % 27 = 0 := by
        omega
      have h4 : X % 27 = 0 ∨ X % 27 = 1 ∨ X % 27 = 2 ∨ X % 27 = 3 ∨ X % 27 = 4 ∨ X % 27 = 5 ∨ X % 27 = 6 ∨ X % 27 = 7 ∨ X % 27 = 8 ∨ X % 27 = 9 ∨ X % 27 = 10 ∨ X % 27 = 11 ∨ X % 27 = 12 ∨ X % 27 = 13 ∨ X % 27 = 14 ∨ X % 27 = 15 ∨ X % 27 = 16 ∨ X % 27 = 17 ∨ X % 27 = 18 ∨ X % 27 = 19 ∨ X % 27 = 20 ∨ X % 27 = 21 ∨ X % 27 = 22 ∨ X % 27 = 23 ∨ X % 27 = 24 ∨ X % 27 = 25 ∨ X % 27 = 26 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [h4, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1' <;> omega
    have h3 : (X + 10) % 27 = 0 := by
      omega
    show X ≡ -10 [ZMOD 3^3]
    simp [Int.ModEq, pow_succ] at *
    all_goals
      omega
  · -- Assume (X ≡ -10 [ZMOD 3^3]), prove (X^3 + X^2 + 10*X + 1 ≡ 0 [ZMOD 3^3])
    intro h
    have h1 : (X + 10) % 27 = 0 := by
      have h2 : X ≡ -10 [ZMOD 3^3] := h
      simp [Int.ModEq, pow_succ] at h2 ⊢
      omega
    have h4 : (X ^ 3 + X ^ 2 + 10 * X + 1) % 27 = 0 := by
      have h4 : X % 27 = 17 := by
        omega
      simp [h4, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      all_goals
        omega
    show X^3 + X^2 + 10*X + 1 ≡ 0 [ZMOD 3^3]
    simp [Int.ModEq, pow_succ] at *
    all_goals
      omega