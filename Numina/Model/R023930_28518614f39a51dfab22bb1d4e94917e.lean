import Mathlib

theorem algebra_166763 (a b c : ℕ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    ∃ p q r : ℤ, p > 0 ∧ ∃ x y z : ℤ, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      p * x ^ 2 + q * x + r = a ^ 3 ∧
      p * y ^ 2 + q * y + r = b ^ 3 ∧
      p * z ^ 2 + q * z + r = c ^ 3 := by
  use (a + b + c : ℤ)
  use -( (a * b + a * c + b * c) : ℤ)
  use ((a * b * c) : ℤ)
  constructor
  · -- Show $p > 0$
    have h11 : (a + b + c > 0) := by
      have h2 : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by 
        by_contra h
        push_neg at h
        have H1 : a = 0 := by omega
        have H2 : b = 0 := by omega
        have H3 : c = 0 := by omega
        have h11 : a = b := by omega
        have h12 : b = c := by omega
        have h13 : a = c := by omega
        tauto
      omega
    norm_num
    omega
  · -- Show existence of x, y, z
    use (a : ℤ)
    use (b : ℤ)
    use (c : ℤ)
    constructor
    · -- Show x ≠ y
      exact_mod_cast ha
    constructor
    · -- Show y ≠ z
      exact_mod_cast hb
    constructor
    · -- Show z ≠ x
      by_contra h_eq
      have h_eq' : (c : ℤ) = (a : ℤ) := by 
        omega
      have h2 : c = a := by 
        norm_num at h_eq' ⊢
        omega 
      tauto
    constructor
    · -- Show p * x ^ 2 + q * x + r = a ^ 3
      norm_num
      <;> ring
    constructor
    · -- Show p * y ^ 2 + q * y + r = b ^ 3
      norm_num
      <;> ring
    · -- Show p * z ^ 2 + q * z + r = c ^ 3
      norm_num
      <;> ring