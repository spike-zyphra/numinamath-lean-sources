import Mathlib

open Real

theorem inequalities_10674 :
    IsLeast {k : ℝ | 0 < k ∧ ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a * b + b * c + c * a + k * (1 / a + 1 / b + 1 / c) ≥ 9} 2 := by 
  constructor
  · -- Show 2 is in the set
    constructor
    · norm_num
    · intro a b c ha hb hc
      have h1 : a * b + b * c + c * a + 2 * (1 / a + 1 / b + 1 / c) ≥ 9 := by
        have h2 : 0 < a * b * c := by
          positivity
        have h3 : a * b + b * c + c * a + 2 * (1 / a + 1 / b + 1 / c) - 9 ≥ 0 := by
          have h10 : a * b + b * c + c * a + 2 * (1 / a + 1 / b + 1 / c) - 9 =
              ( (a * b + b * c + c * a) * (a * b * c) + 2 * ( (b * c) + (a * c) + (a * b) ) - 9 * (a * b * c) ) / ( a * b * c ) := by
            field_simp
            ring
          rw [h10] 
          have h11 : (a * b + b * c + c * a) * (a * b * c) + 2 * ( (b * c) + (a * c) + (a * b) ) - 9 * (a * b * c) ≥ 0 := by
            nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a * b * c - 1),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                mul_pos (mul_pos ha hb) hc
            ]
          have h12 : a * b * c > 0 := by
            positivity
          have h13 : ( (a * b + b * c + c * a) * (a * b * c) + 2 * ( (b * c) + (a * c) + (a * b) ) - 9 * (a * b * c) ) / ( a * b * c ) ≥ 0 := by
            apply div_nonneg
            linarith
            positivity
          linarith
        linarith
      linarith
  · -- Show 2 is the smallest element in the set 
    intro k hk
    rcases hk with ⟨hk_pos, hk_ineq⟩
    have h1 : k ≥ 2 := by
      have h2 := hk_ineq 1 1 1 (by norm_num) (by norm_num) (by norm_num)
      norm_num at h2 
      nlinarith
    linarith