import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_213648 :
    {x : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ x = (a + b + c) * (1 / a + 1 / b + 1 / c)} = 
    Ici 9 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · -- Assume x ∈ {y | ...}, prove x ≥ 9
    rintro ⟨a, b, c, ha, hb, hc, hx⟩
    have h1 : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 9 := by
      have h4 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 ≥ 0 := by
        have h5 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 =
            ((a + b + c) * (b * c + a * c + a * b) - 9 * (a * b * c)) / (a * b * c) := by
          field_simp
          ring
        rw [h5]
        have h6 : (a + b + c) * (b * c + a * c + a * b) - 9 * (a * b * c) ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
              sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
              sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
        have h7 : ((a + b + c) * (b * c + a * c + a * b) - 9 * (a * b * c)) / (a * b * c) ≥ 0 := by
          have h8 : a * b * c > 0 := by
            apply mul_pos
            apply mul_pos
            all_goals linarith
          apply div_nonneg
          linarith
          all_goals linarith
        linarith
      linarith
    have h2 : x = (a + b + c) * (1 / a + 1 / b + 1 / c) := hx
    nlinarith
  · -- Assume x ≥ 9, prove x ∈ {y | ...}
    intro hx
    by_cases h : x = 9
    · -- x = 9
      rw [h]
      use 1, 1, 1
      norm_num
    · -- x > 9
      have hx2 : x > 9 := by
        by_contra h'
        push_neg at h'
        have : x = 9 := by linarith
        tauto
      have h11 : ∃ t : ℝ, t > 0 ∧ 2 * t ^ 2 + (5 - x) * t + 2 = 0 := by
        use ((x - 5) + Real.sqrt ((5 - x) ^ 2 - 16)) / 4
        constructor
        ·
          have h101 : (5 - x) ^ 2 - 16 ≥ 0 := by
            nlinarith [sq_nonneg (x - 9)]
          have h102 : ((x - 5) + Real.sqrt ((5 - x) ^ 2 - 16)) / 4 > 0 := by
            have h100 : Real.sqrt ((5 - x) ^ 2 - 16) ≥ 0 := by positivity
            nlinarith [Real.sqrt_nonneg ((5 - x) ^ 2 - 16), Real.sq_sqrt (show (0 : ℝ) ≤ (5 - x) ^ 2 - 16 by nlinarith [sq_nonneg (x - 9)])]
          linarith
        ·
          have h101 : (5 - x) ^ 2 - 16 ≥ 0 := by
            nlinarith [sq_nonneg (x - 9)]
          nlinarith [Real.sqrt_nonneg ((5 - x) ^ 2 - 16), Real.sq_sqrt (show (0 : ℝ) ≤ (5 - x) ^ 2 - 16 by nlinarith [sq_nonneg (x - 9)])]
      rcases h11 with ⟨t, ht_pos, heq⟩
      use t, 1, 1
      constructor
      · -- Show a > 0
        linarith
      constructor
      · -- Show b > 0
        norm_num
      constructor
      · -- Show c > 0
        norm_num
      · -- Show x = (t + 1 + 1) * (1 / t + 1 / 1 + 1 / 1)
        have h13 : x = (t + 1 + 1) * (1 / t + 1 / 1 + 1 / 1) := by
          have h16 : 2 * t ^ 2 + (5 - x) * t + 2 = 0 := by linarith
          have h17 : t > 0 := ht_pos
          field_simp at h16 ⊢
          nlinarith
        linarith