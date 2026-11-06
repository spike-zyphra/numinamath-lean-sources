import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_598961 :
  IsGreatest {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 ∧ x = sqrt (4 * a + 1) + sqrt (4 * b + 1) + sqrt (4 * c + 1)} (sqrt 21) := by
  constructor
  · -- Show that sqrt(21) is in the set
    use 1 / 3, 1 / 3, 1 / 3
    constructor
    · norm_num -- a > 0
    constructor
    · norm_num -- b > 0
    constructor
    · norm_num -- c > 0
    constructor
    · norm_num -- a + b + c = 1
    · -- Show sqrt 21 = sqrt (4 * (1/3) + 1) + ... (symmetrized)
      have h1 : sqrt (21) = sqrt 7 * sqrt 3 := by
        calc
          sqrt 21 = sqrt (7 * 3) := by norm_num
          _ = sqrt 7 * sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
      have h2 : sqrt (4 * (1 / 3 : ℝ) + 1) = sqrt (7 / 3 : ℝ) := by norm_num
      rw [h2]
      have h3 : sqrt (7 / 3 : ℝ) + sqrt (7 / 3 : ℝ) + sqrt (7 / 3 : ℝ) = 3 * sqrt (7 / 3 : ℝ) := by ring
      rw [h3]
      have h4 : 3 * sqrt (7 / 3 : ℝ) = sqrt 7 * sqrt 3 := by
        have h5 : sqrt (7 / 3 : ℝ) = sqrt 7 / sqrt 3 := by
          field_simp [Real.sqrt_div]
          all_goals
            norm_num
            <;> try { nlinarith }
        rw [h5]
        have h6 : sqrt 3 > 0 := by
          apply Real.sqrt_pos.mpr
          norm_num
        field_simp
        <;> try { nlinarith }
        <;> ring_nf <;> try { field_simp }
        <;> try { nlinarith }
      nlinarith [h1, h4, Real.sqrt_pos.mpr (show (21 : ℝ) > 0 by norm_num)]
  · -- Show that sqrt 21 is greatest
    rintro x ⟨a, b, c, ha, hb, hc, hsum, hx⟩
    have h1 : sqrt (4 * a + 1) + sqrt (4 * b + 1) + sqrt (4 * c + 1) ≤ sqrt 21 := by
      have h2 : (sqrt (4 * a + 1) + sqrt (4 * b + 1) + sqrt (4 * c + 1)) ^ 2 ≤ 21 := by
        nlinarith [sq_nonneg (sqrt (4 * a + 1) - sqrt (4 * b + 1)), sq_nonneg (sqrt (4 * a + 1) - sqrt (4 * c + 1)), sq_nonneg (sqrt (4 * b + 1) - sqrt (4 * c + 1)),
          Real.sq_sqrt (show (4 * a + 1) ≥ 0 by linarith), Real.sq_sqrt (show (4 * b + 1) ≥ 0 by linarith), Real.sq_sqrt (show (4 * c + 1) ≥ 0 by linarith),
          mul_nonneg (Real.sqrt_nonneg (4 * a + 1)) (Real.sqrt_nonneg (4 * b + 1)), mul_nonneg (Real.sqrt_nonneg (4 * a + 1)) (Real.sqrt_nonneg (4 * c + 1)), mul_nonneg (Real.sqrt_nonneg (4 * b + 1)) (Real.sqrt_nonneg (4 * c + 1)),
          hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      have h3 : (sqrt (4 * a + 1) + sqrt (4 * b + 1) + sqrt (4 * c + 1)) ≥ 0 := by positivity
      have h4 : sqrt 21 ≥ 0 := by positivity
      nlinarith [Real.sq_sqrt (show (21 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (4 * a + 1) ≥ 0 by linarith), Real.sq_sqrt (show (4 * b + 1) ≥ 0 by linarith), Real.sq_sqrt (show (4 * c + 1) ≥ 0 by linarith)]
    linarith [h1, hx]