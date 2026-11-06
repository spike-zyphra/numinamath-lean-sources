import Mathlib

open Real

theorem inequalities_277140 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a + b + c + d) / 4 ≥ (a * b * c * d) ^ ((1 : ℝ) / 4) := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h4 : 0 < d := hd

  have h5 : (a * b * c * d) ^ ((1 : ℝ) / 4) ≤ (a + b + c + d) / 4 := by
    have h6 : (a * b * c * d) ^ ((1 : ℝ) / 4) = ((a: ℝ) * (b: ℝ) * (c: ℝ) * (d: ℝ)) ^ ((1 : ℝ) / 4) := by rfl
    rw [h6] at *
    
    have h7 : ((a: ℝ) * (b: ℝ) * (c: ℝ) * (d: ℝ)) ^ ((1 : ℝ) / 4) ≤ (a + b + c + d) / 4 := by
      have h8 : ((a: ℝ) * (b: ℝ) * (c: ℝ) * (d: ℝ)) ^ ((1 : ℝ) / 4) =
          (a ^ ((1 : ℝ) / 4) * b ^ ((1 : ℝ) / 4) * c ^ ((1 : ℝ) / 4) * d ^ ((1 : ℝ) / 4)) := by
        rw [← Real.mul_rpow]
        rw [← Real.mul_rpow]
        rw [← Real.mul_rpow]
        all_goals
          try positivity

      rw [h8]
      have h9 : a ^ ((1 : ℝ) / 4) * b ^ ((1 : ℝ) / 4) * c ^ ((1 : ℝ) / 4) * d ^ ((1 : ℝ) / 4) ≤ ( (1 / 4) * a + (1 / 4) * b + (1 / 4) * c + (1 / 4) * d ) := by
        apply Real.geom_mean_le_arith_mean4_weighted
        all_goals
          try norm_num
        all_goals
          try positivity

      have h10 : ( (1 / 4) * a + (1 / 4) * b + (1 / 4) * c + (1 / 4) * d ) = (a + b + c + d) / 4 := by 
        ring

      linarith [h9, h10]

    linarith
  linarith