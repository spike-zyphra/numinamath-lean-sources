import Mathlib

theorem number_theory_7346 (x : ℤ) : x^2 ≡ 19 [ZMOD 45] ↔
    x ≡ 8 [ZMOD 45] ∨ x ≡ -8 [ZMOD 45] ∨ x ≡ 17 [ZMOD 45] ∨ x ≡ -17 [ZMOD 45] := by 
  simp [Int.ModEq]
  constructor
  · -- Assume $x^2 \equiv 19 \pmod{45}$, prove $x \equiv 8, -8, 17, -17 \pmod{45}$.
    intro h
    have h1 : x % 45 = 8 ∨ x % 45 = 17 ∨ x % 45 = 28 ∨ x % 45 = 37 := by
      have h1 : x % 9 = 1 ∨ x % 9 = 8 := by
        have h9 : (x ^ 2 : ℤ) % 9 = 1 := by 
          omega
        have : (x % 9 : ℤ) = 0 ∨ (x % 9 : ℤ) = 1 ∨ (x % 9 : ℤ) = 2 ∨ (x % 9 : ℤ) = 3 ∨ (x % 9 : ℤ) = 4 ∨ (x % 9 : ℤ) = 5 ∨ (x % 9 : ℤ) = 6 ∨ (x % 9 : ℤ) = 7 ∨ (x % 9 : ℤ) = 8 := by omega
        rcases this with (h | h | h | h | h | h | h | h | h) <;> simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.sub_emod] at h9 <;> tauto
      have h5 : (x ^ 2 : ℤ) % 5 = 4 := by 
        omega
      have h2 : (x % 5 : ℤ) = 2 ∨ (x % 5 : ℤ) = 3 := by
        have : (x % 5 : ℤ) = 0 ∨ (x % 5 : ℤ) = 1 ∨ (x % 5 : ℤ) = 2 ∨ (x % 5 : ℤ) = 3 ∨ (x % 5 : ℤ) = 4 := by omega
        rcases this with (h | h | h | h | h) <;> simp [Int.add_emod, Int.mul_emod, pow_two, h, Int.sub_emod] at h5 <;> tauto
      rcases h1 with (h1 | h1)
      · -- x ≡ 1 (mod 9)
        rcases h2 with (h2 | h2)
        · -- x ≡ 2 (mod 5)
          omega
        · -- x ≡ 3 (mod 5)
          omega
      · -- x ≡ 8 (mod 9)
        rcases h2 with (h2 | h2)
        · -- x ≡ 2 (mod 5)
          omega
        · -- x ≡ 3 (mod 5)
          omega
    omega
  · -- Assume $x \equiv 8, -8, 17, -17 \pmod{45}$, prove $x^2 \equiv 19 \pmod{45}$.
    rintro (h | h | h | h)
    · -- x ≡ 8 [ZMOD 45]
      norm_num [Int.ModEq] at h ⊢
      have h1 : x % 45 = 8 := by 
        omega
      have : x ^ 2 % 45 = 19 := by
        have h2 : x % 45 = 8 := h1
        simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      omega
    · -- x ≡ -8 [ZMOD 45]
      norm_num [Int.ModEq] at h ⊢
      have h1 : x % 45 = 37 := by 
        omega
      have : x ^ 2 % 45 = 19 := by
        have h2 : x % 45 = 37 := h1
        simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      omega
    · -- x ≡ 17 [ZMOD 45]
      norm_num [Int.ModEq] at h ⊢
      have h1 : x % 45 = 17 := by 
        omega
      have : x ^ 2 % 45 = 19 := by
        have h2 : x % 45 = 17 := h1
        simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      omega
    · -- x ≡ -17 [ZMOD 45]
      norm_num [Int.ModEq] at h ⊢
      have h1 : x % 45 = 28 := by 
        omega
      have : x ^ 2 % 45 = 19 := by
        have h2 : x % 45 = 28 := h1
        simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      omega