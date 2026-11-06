import Mathlib

theorem number_theory_166351 :
  {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x^3 - y^3 = x * y + 61} = {(6, 5)} := by 
  ext ⟨x, y⟩
  simp
  constructor 
  · -- Forward direction (→): prove (x,y) = (6,5)
    rintro ⟨hx, hy, h⟩
    have h1 : x ^ 3 = y ^ 3 + x * y + 61 := by 
      omega
    have h2 : x > y := by
      nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, mul_pos hx hy, h1]
    have h3 : y ≤ 6 := by 
      by_contra h9
      push_neg at h9
      have h9 : y ≥ 7 := by nlinarith 
      have h7 : x ≤ 6 := by 
        nlinarith [sq_nonneg ((x : ℤ) - (1)), sq_nonneg ((y : ℤ) - (1)), sq_nonneg ((x : ℤ) - (y : ℤ)), h1, sq_nonneg ((y : ℤ) - (6 : ℤ)), mul_pos hx hy, sq_nonneg ((x * (x) : ℤ) - (y * (y) : ℤ))]
      interval_cases x <;> try { 
        omega 
      }
    have h4 : x ≤ 23 := by
      interval_cases y 
      <;> try { 
        nlinarith [sq_nonneg ((x : ℤ) - 11 : ℤ), sq_nonneg ((x * x : ℤ) - (121 : ℤ)), sq_nonneg ((x : ℤ) * (1 : ℤ) - (66 : ℤ))]
      }
    interval_cases y 
    <;> interval_cases x 
    <;> omega 
  · -- Assume the right side 
    rintro ⟨rfl, rfl⟩ 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    · norm_num