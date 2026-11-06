import Mathlib

theorem number_theory_6262 (x : ℤ) (h : 4*x^2+27*x-7≡0[ZMOD 15]) :
    x≡-7[ZMOD 15] ∨ x≡-2[ZMOD 15] ∨ x≡-1[ZMOD 15] ∨ x≡4[ZMOD 15] := by
  have h1 : (4 * x ^ 2 + 27 * x - 7 : ℤ) % 15 = 0 := h
  have h2 : x % 15 = 0 ∨ x % 15 = 1 ∨ x % 15 = 2 ∨ x % 15 = 3 ∨ x % 15 = 4 ∨
      x % 15 = 5 ∨ x % 15 = 6 ∨ x % 15 = 7 ∨ x % 15 = 8 ∨ x % 15 = 9 ∨
      x % 15 = 10 ∨ x % 15 = 11 ∨ x % 15 = 12 ∨ x % 15 = 13 ∨ x % 15 = 14 := by
    omega
  rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [Int.ModEq, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] at h1 ⊢
  <;> omega