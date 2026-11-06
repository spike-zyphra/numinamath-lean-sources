import Mathlib

open Real

theorem inequalities_40112 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : min (min (a * b) (b * c)) (c * a) ≥ 1) :
    ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ ((1 : ℝ) / 3) ≤
    ((a + b + c) / 3) ^ 2 + 1 := by

  have h1 : a * b ≥ 1 := by
    by_contra h1
    push_neg at h1
    have h2 : min (min (a * b) (b * c)) (c * a) < 1 := by
      have h3 : a * b < 1 := by linarith
      have h4 : min (a * b) (b * c) ≤ a * b := by
        cases min_cases (a * b) (b * c) with
        | inl h => linarith
        | inr h => linarith
      have h5 : min (min (a * b) (b * c)) (c * a) ≤ min (a * b) (b * c) := by
        cases min_cases (min (a * b) (b * c)) (c * a) with
        | inl h => linarith
        | inr h => linarith
      nlinarith
    linarith

  have h2 : b * c ≥ 1 := by
    by_contra h2
    push_neg at h2
    have h3 : min (min (a * b) (b * c)) (c * a) < 1 := by
      have h4 : b * c < 1 := by linarith
      have h5 : min (a * b) (b * c) ≤ b * c := by
        cases min_cases (a * b) (b * c) with
        | inl h => linarith
        | inr h => linarith
      have h6 : min (min (a * b) (b * c)) (c * a) ≤ min (a * b) (b * c) := by
        cases min_cases (min (a * b) (b * c)) (c * a) with
        | inl h => linarith
        | inr h => linarith
      nlinarith
    linarith

  have h3 : c * a ≥ 1 := by
    by_contra h3
    push_neg at h3
    have h4 : min (min (a * b) (b * c)) (c * a) < 1 := by
      have h5 : c * a < 1 := by linarith
      have h6 : min (min (a * b) (b * c)) (c * a) ≤ c * a := by
        have h7 : min (min (a * b) (b * c)) (c * a) ≤ c * a := by
          cases min_cases (min (a * b) (b * c)) (c * a) with
          | inl h => linarith
          | inr h => linarith
        linarith
      nlinarith
    linarith

  have h4 : ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ ((1 : ℝ) / 3) ≤ ((a + b + c) / 3) ^ 2 + 1 := by
    have h5 : (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ≤ (((a + b + c) / 3) ^ 2 + 1) ^ 3 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        mul_nonneg (show 0 ≤ a * b - 1 by nlinarith) (show 0 ≤ b * c - 1 by nlinarith),
        mul_nonneg (show 0 ≤ b * c - 1 by nlinarith) (show 0 ≤ c * a - 1 by nlinarith),
        mul_nonneg (show 0 ≤ a * b - 1 by nlinarith) (show 0 ≤ c * a - 1 by nlinarith)
      ]
    have h14 : ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ ((1 : ℝ) / 3) ≤ ((( (a + b + c) / 3 ) ^ 2 + 1 ) ^ 3) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow
      · -- Show 0 ≤ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)
        positivity
      · -- Show (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ≤ ((a + b + c) / 3) ^ 2 + 1) ^ 3
        linarith [h5]
      all_goals
        norm_num

    have h15 : (( ( (a + b + c) / 3 ) ^ 2 + 1 ) ^ 3) ^ ((1 : ℝ) / 3) = ((a + b + c) / 3) ^ 2 + 1 := by
      have h16 : (( ( (a + b + c) / 3 ) ^ 2 + 1 ) ^ 3) ^ ((1 : ℝ) / 3) = ((a + b + c) / 3) ^ 2 + 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          positivity
      linarith [h16]

    linarith [h14, h15]

  exact h4