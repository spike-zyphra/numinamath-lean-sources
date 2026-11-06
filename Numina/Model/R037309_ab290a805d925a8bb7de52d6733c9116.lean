import Mathlib

open Real

theorem inequalities_187294 (p : ℝ) (hp : p > 0) :
    2 + 1 / (2 * (p^2 + p)) > (2 * p + 1) * (sqrt ((p + 1) / p) - sqrt (p / (p + 1))) ∧
    (2 * p + 1) * (sqrt ((p + 1) / p) - sqrt (p / (p + 1))) > 2 := by

  have h1 : sqrt ((p + 1) / p) = Real.sqrt (p + 1) / Real.sqrt p := by
    have hp' : p > 0 := hp
    field_simp [Real.sqrt_div]

  have h2 : sqrt (p / (p + 1)) = Real.sqrt p / Real.sqrt (p + 1) := by
    have hp' : p > 0 := hp
    have hp3 : p + 1 > 0 := by linarith
    field_simp [Real.sqrt_div]

  have h3 : (2 * p + 1) * (sqrt ((p + 1) / p) - sqrt (p / (p + 1))) = (2 * p + 1) / Real.sqrt (p * (p + 1)) := by
    rw [h1, h2]
    have hp' : p > 0 := hp
    have hp3 : p + 1 > 0 := by linarith
    have h4 : Real.sqrt (p * (p + 1)) = Real.sqrt p * Real.sqrt (p + 1) := by
      rw [Real.sqrt_mul (by nlinarith)]
    rw [h4]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < p by linarith : p > 0), Real.sqrt_pos.mpr (show 0 < p + 1 by linarith : p + 1 > 0), Real.sq_sqrt (show 0 ≤ p by linarith), Real.sq_sqrt (show 0 ≤ p + 1 by linarith)]

  have h4 : (2 * p + 1) * (sqrt ((p + 1) / p) - sqrt (p / (p + 1))) > 2 := by
    rw [h3]
    have hp5 : Real.sqrt (p * (p + 1)) > 0 := by
      apply Real.sqrt_pos.mpr
      positivity
    have h7 : (2 * p + 1) > 2 * Real.sqrt (p * (p + 1)) := by
      have h8 : ((2 * p + 1) : ℝ) ^ 2 > 4 * p * (p + 1) := by
        nlinarith [sq_pos_of_pos hp]
      have h9 : (2 * Real.sqrt (p * (p + 1))) ^ 2 = 4 * p * (p + 1) := by
        calc
          (2 * Real.sqrt (p * (p + 1))) ^ 2 = 4 * (Real.sqrt (p * (p + 1)) ^ 2) := by ring
          _ = 4 * (p * (p + 1)) := by rw [Real.sq_sqrt (by positivity)]
          _ = 4 * p * (p + 1) := by ring
      have h10 : (2 * p + 1) ≥ 0 := by nlinarith
      have h11 : (2 * Real.sqrt (p * (p + 1))) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (p * (p + 1)), Real.sq_sqrt (show 0 ≤ (p * (p + 1)) by positivity)]
    have hp6 : Real.sqrt (p * (p + 1)) > 0 := hp5
    have hp7 : (2 * p + 1) / Real.sqrt (p * (p + 1)) > (2 : ℝ) := by
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith

  have h5 : 2 + 1 / (2 * (p^2 + p)) > (2 * p + 1) * (sqrt ((p + 1) / p) - sqrt (p / (p + 1))) := by
    rw [h3]
    have hp5 : Real.sqrt (p * (p + 1)) > 0 := by
      apply Real.sqrt_pos.mpr
      positivity
    have h7 : (2 * p + 1) > 2 * Real.sqrt (p * (p + 1)) := by
      have h8 : ((2 * p + 1) : ℝ) ^ 2 > 4 * p * (p + 1) := by
        nlinarith [sq_pos_of_pos hp]
      have h9 : (2 * Real.sqrt (p * (p + 1))) ^ 2 = 4 * p * (p + 1) := by
        calc
          (2 * Real.sqrt (p * (p + 1))) ^ 2 = 4 * (Real.sqrt (p * (p + 1)) ^ 2) := by ring
          _ = 4 * (p * (p + 1)) := by rw [Real.sq_sqrt (by positivity)]
          _ = 4 * p * (p + 1) := by ring
      have h10 : (2 * p + 1) ≥ 0 := by nlinarith
      have h11 : (2 * Real.sqrt (p * (p + 1))) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (p * (p + 1)), Real.sq_sqrt (show 0 ≤ (p * (p + 1)) by positivity)]
    have h11 : (2 + 1 / (2 * (p^2 + p)) - ((2 * p + 1) / Real.sqrt (p * (p + 1))) ) > 0 := by
      have hp12 : 0 < Real.sqrt (p * (p + 1)) := by positivity
      have hp13 : 0 < 2 * (p^2 + p) := by positivity
      have h12 : (2 + 1 / (2 * (p^2 + p)) - ((2 * p + 1) / Real.sqrt (p * (p + 1))) ) =
          ( (2 * (2 * p^2 + 2 * p) * Real.sqrt (p * (p + 1)) + Real.sqrt (p * (p + 1)) - (2 * p + 1) * (2 * p^2 + 2 * p) ) ) / ( (2 * (p^2 + p)) * Real.sqrt (p * (p + 1)) ) := by
        field_simp
        <;> ring
      rw [h12]
      apply div_pos
      have h13 : (2 * (2 * p^2 + 2 * p) * Real.sqrt (p * (p + 1)) + Real.sqrt (p * (p + 1)) - (2 * p + 1) * (2 * p^2 + 2 * p) ) > 0 := by
        have hp5 : Real.sqrt (p * (p + 1)) > 0 := by
          apply Real.sqrt_pos.mpr
          positivity
        have h7 : (2 * p + 1) > 2 * Real.sqrt (p * (p + 1)) := by
          have h8 : ((2 * p + 1) : ℝ) ^ 2 > 4 * p * (p + 1) := by
            nlinarith [sq_pos_of_pos hp]
          have h9 : (2 * Real.sqrt (p * (p + 1))) ^ 2 = 4 * p * (p + 1) := by
            calc
              (2 * Real.sqrt (p * (p + 1))) ^ 2 = 4 * (Real.sqrt (p * (p + 1)) ^ 2) := by ring
              _ = 4 * (p * (p + 1)) := by rw [Real.sq_sqrt (by positivity)]
              _ = 4 * p * (p + 1) := by ring
          have h10 : (2 * p + 1) ≥ 0 := by nlinarith
          have h11 : (2 * Real.sqrt (p * (p + 1))) ≥ 0 := by positivity
          nlinarith [Real.sqrt_nonneg (p * (p + 1)), Real.sq_sqrt (show 0 ≤ (p * (p + 1)) by positivity)]
        nlinarith [Real.sq_sqrt (show 0 ≤ (p * (p + 1)) by positivity), Real.sqrt_nonneg (p * (p + 1)), sq_nonneg (Real.sqrt (p * (p + 1)) ^ 2 - (p * (p + 1)) ) ]
      linarith
      all_goals positivity

    linarith

  constructor
  · linarith
  · linarith