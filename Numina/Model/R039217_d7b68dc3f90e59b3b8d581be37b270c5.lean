import Mathlib

theorem algebra_302380 : {(a, b, c) : ℤ × ℤ × ℤ | a < b ∧ b < c ∧ a * b + b * c + c * a = a * b * c ∧ a ≥ 1} = {(2, 3, 6)} := by
  ext ⟨a, b, c⟩ 
  simp 
  constructor 
  · -- Prove that if $(a,b,c)$ is in the left side, then it must be $(2,3,6)$.
    rintro ⟨h1, h2, h3, h4⟩ 
    have ha : a > 0 := by 
      nlinarith
    have hb : b > 0 := by 
      nlinarith [h1]
    have hc : c > 0 := by 
      nlinarith [h1, h2]
    have h5 : (a - 1) * (b - 1) * (c - 1) = a + b + c - 1 := by 
      nlinarith [h3]
    have ha1 : a ≤ 3 := by
      have hk1 : a ≤ 3 := by
        nlinarith [mul_pos (show 0 < (b - a : ℤ) by omega) (show 0 < (c - b : ℤ) by omega), sq_nonneg (a - 2 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (c - 6 : ℤ), sq_pos_of_pos (show 0 < (b - a : ℤ) by omega), sq_pos_of_pos (show 0 < (c - b : ℤ) by omega)]
      omega
    interval_cases a <;> try { 
      omega 
    } <;> try { 
      have h11 : b ≤ 12 := by 
        nlinarith [sq_nonneg (b - 3 : ℤ), sq_nonneg (c - 6 : ℤ)]
      have h12 : b ≥ 1 := by 
        omega 
      interval_cases b <;> try { 
        omega 
      } <;> try { 
        have h13 : c ≤ 12 := by 
          nlinarith 
        have h14 : c ≥ 1 := by 
          omega 
        interval_cases c <;> omega 
      }
    }
  · -- Show the right side is contained in the left side.
    rintro ⟨rfl, rfl, rfl⟩ 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    all_goals norm_num