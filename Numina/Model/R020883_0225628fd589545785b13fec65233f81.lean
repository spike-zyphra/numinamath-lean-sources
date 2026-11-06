import Mathlib

open BigOperators Complex Filter Finset Function Metric Topology

lemma lemma_1 {z : ℕ → ℂ}
  (hz : ∀ n, z n = ∏ k ∈ Icc 1 n, (1 + I / Real.sqrt k)) :
  ∀ n, abs (z n) = Real.sqrt (n + 1) := by
  intro n
  rw [hz n]
  have h1 : ∀ n : ℕ, abs (∏ k in Icc 1 n, (1 + Complex.I / Real.sqrt k) : ℂ) = Real.sqrt (n + 1) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [prod_Icc_succ_top (by linarith)]
      have h3 : abs ((∏ k in Icc 1 n, (1 + Complex.I / Real.sqrt k) : ℂ) * (1 + Complex.I / Real.sqrt (n + 1 : ℕ)) ) = abs ((∏ k in Icc 1 n, (1 + Complex.I / Real.sqrt k) : ℂ)) * abs ((1 + Complex.I / Real.sqrt (n + 1 : ℕ)) : ℂ) := by
        simp [norm_mul]
      rw [h3]
      rw [ih]
      have h4 : abs ((1 + Complex.I / Real.sqrt (n + 1 : ℕ) : ℂ) ) = Real.sqrt (( (n + 2 : ℝ) ) / ( (n + 1 : ℝ) )) := by
        simp [Complex.abs, Complex.normSq]
        field_simp
        ring_nf
      rw [h4]
      have h5 : Real.sqrt ((n + 1 : ℝ)) * Real.sqrt (( (n + 2 : ℝ) ) / ( (n + 1 : ℝ) )) = Real.sqrt ((n + 2 : ℝ)) := by
        have h6 : Real.sqrt ((n + 1 : ℝ)) * Real.sqrt (( (n + 2 : ℝ) ) / ( (n + 1 : ℝ) ) ) = Real.sqrt ( (n + 1 : ℝ) * ( (n + 2 : ℝ) / (n + 1 : ℝ) ) ) := by
          rw [← Real.sqrt_mul (by
            positivity
          )]
        rw [h6]
        have h7 : (n + 1 : ℝ) * ( (n + 2 : ℝ) / (n + 1 : ℝ) ) = (n + 2 : ℝ) := by
          field_simp [(show (n + 1 : ℝ) ≠ 0 by positivity)]
        rw [h7]
      rw [h5]
      simp [show (n + 1 + 1 : ℝ) = (n + 2 : ℝ) by ring]
  simpa using h1 n


theorem algebra_305263 {z : ℕ → ℂ}
  (hz : ∀ n, z n = ∏ i ∈ Icc 1 n, (1 + I / Real.sqrt i)) :
  abs (z 2014 - z 2015) = 1 := by

  have h1 : z 2015 = z 2014 * (1 + I / Real.sqrt 2015) := by
    rw [hz 2015, hz 2014]
    rw [show 2015 = 2014 + 1 by norm_num]
    rw [prod_Icc_succ_top (by norm_num)]
    all_goals
      simp
  have h2 : z 2014 - z 2015 = z 2014 * (-I / Real.sqrt 2015 : ℂ) := by
    rw [h1]
    ring_nf
  have h3 : abs (z 2014 - z 2015) = abs (z 2014) * abs ((-I / Real.sqrt 2015 : ℂ) ) := by
    rw [h2]
    have h4 : abs (z 2014 * (-I / Real.sqrt 2015 : ℂ)) = abs (z 2014) * abs ((-I / Real.sqrt 2015 : ℂ) ) := by
      simp [norm_mul]
    simpa using h4
  have h4 : abs ((-I / Real.sqrt 2015 : ℂ) ) = (1 / Real.sqrt 2015 : ℝ) := by
    simp [Complex.abs, Complex.normSq]
    all_goals
      field_simp
  have h5 : abs (z 2014) = Real.sqrt 2015 := by
    have h6 : abs (z 2014) = Real.sqrt (2014 + 1 : ℝ) := by
      apply lemma_1 hz
    have h7 : (2014 + 1 : ℝ) = (2015 : ℝ) := by norm_num
    rw [h7] at h6
    linarith
  rw [h3, h4, h5]
  have h8 : Real.sqrt (2015 : ℝ) > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num
  field_simp