import Mathlib

theorem number_theory_6617 (x : ℤ) :
    (x^2 + 1) * (x + 1) * x ≡ -1 [ZMOD 41] ↔
    x ≡ 10 [ZMOD 41] ∨ x ≡ 18 [ZMOD 41] ∨ x ≡ 16 [ZMOD 41] ∨ x ≡ 37 [ZMOD 41] := by
  constructor
  · -- Forward direction: if (x^2 + 1)(x + 1)x ≡ -1 (mod 41), then x ≡ 10, 18, 16, or 37 (mod 41)
    intro h
    simp [Int.ModEq] at h ⊢
    have h1 : x % 41 = 10 ∨ x % 41 = 18 ∨ x % 41 = 16 ∨ x % 41 = 37 := by
      have h2 : x % 41 = 0 ∨ x % 41 = 1 ∨ x % 41 = 2 ∨ x % 41 = 3 ∨ x % 41 = 4 ∨ x % 41 = 5 ∨
        x % 41 = 6 ∨ x % 41 = 7 ∨ x % 41 = 8 ∨ x % 41 = 9 ∨ x % 41 = 10 ∨ x % 41 = 11 ∨
        x % 41 = 12 ∨ x % 41 = 13 ∨ x % 41 = 14 ∨ x % 41 = 15 ∨ x % 41 = 16 ∨ x % 41 = 17 ∨
        x % 41 = 18 ∨ x % 41 = 19 ∨ x % 41 = 20 ∨ x % 41 = 21 ∨ x % 41 = 22 ∨ x % 41 = 23 ∨
        x % 41 = 24 ∨ x % 41 = 25 ∨ x % 41 = 26 ∨ x % 41 = 27 ∨ x % 41 = 28 ∨ x % 41 = 29 ∨
        x % 41 = 30 ∨ x % 41 = 31 ∨ x % 41 = 32 ∨ x % 41 = 33 ∨ x % 41 = 34 ∨ x % 41 = 35 ∨
        x % 41 = 36 ∨ x % 41 = 37 ∨ x % 41 = 38 ∨ x % 41 = 39 ∨ x % 41 = 40 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
        try { 
          simp [h2, Int.add_emod, Int.mul_emod, pow_two, pow_succ] at h ⊢
          <;> omega
        }
    assumption
  · -- Backward direction: if x ≡ 10, 18, 16, or 37 (mod 41), then (x^2 + 1)(x + 1)x ≡ -1 (mod 41)
    rintro (h1 | h1 | h1 | h1)
    · -- Case x ≡ 10
      have h2 : x % 41 = 10 := h1
      simp [Int.ModEq, Int.mul_emod, Int.add_emod, pow_two, pow_succ, h2]
      <;> omega
    · -- Case x ≡ 18
      have h2 : x % 41 = 18 := h1
      simp [Int.ModEq, Int.mul_emod, Int.add_emod, pow_two, pow_succ, h2]
      <;> omega
    · -- Case x ≡ 16
      have h2 : x % 41 = 16 := h1
      simp [Int.ModEq, Int.mul_emod, Int.add_emod, pow_two, pow_succ, h2]
      <;> omega
    · -- Case x ≡ 37
      have h2 : x % 41 = 37 := h1
      simp [Int.ModEq, Int.mul_emod, Int.add_emod, pow_two, pow_succ, h2]
      <;> omega