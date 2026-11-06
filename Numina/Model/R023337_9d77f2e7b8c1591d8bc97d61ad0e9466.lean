import Mathlib

open Real

theorem calculus_2108 : ∫ x in (0)..1, sqrt ((1 + x) * (2 + x ^ 3)) ≤ 2 := by 
  have h1 : ∀ x : ℝ, x ≥ 0 → x ≤ 1 → sqrt ((1 + x) * (2 + x ^ 3)) ≤ x + 3 / 2 := by
    intro x hx1 hx2 
    have h2 : (1 + x) * (2 + x ^ 3) ≥ 0 := by
      apply mul_nonneg
      all_goals
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2), sq_nonneg (x ), sq_nonneg (x - 1)]
    have h3 : x + 3 / 2 ≥ 0 := by
      nlinarith 
    have h4 : sqrt ((1 + x) * (2 + x ^ 3)) = Real.sqrt ((1 + x) * (2 + x ^ 3)) := by 
      rfl 
    have h5 : Real.sqrt ((1 + x) * (2 + x ^ 3)) ≤ x + 3 / 2 := by
      have h6 : (Real.sqrt ((1 + x) * (2 + x ^ 3))) ^ 2 ≤ (x + 3 / 2) ^ 2 := by
        have h6a : (Real.sqrt ((1 + x) * (2 + x ^ 3))) ^ 2 = (1 + x) * (2 + x ^ 3) := by
          rw [Real.sq_sqrt]
          nlinarith
        have h6b : (x + 3 / 2) ^ 2 ≥ (1 + x) * (2 + x ^ 3) := by 
          nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x ^ 2 - 1), sq_nonneg (x * (x - 1 / 2)), sq_nonneg ((x + 1 / 2) * (x - 1 / 2)), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
        nlinarith [h6a, h6b]
      have h7 : Real.sqrt ((1 + x) * (2 + x ^ 3)) ≥ 0 := by positivity 
      have h8 : (x + 3 / 2 : ℝ) ≥ 0 := by nlinarith 
      nlinarith [Real.sqrt_nonneg ((1 + x) * (2 + x ^ 3))]
    linarith [h4, h5]
 
  have h2 : ∫ x in (0)..1, sqrt ((1 + x) * (2 + x ^ 3)) ≤ ∫ x in (0)..1, (x + 3 / 2 : ℝ) := by
    have hf : IntervalIntegrable (fun x : ℝ => sqrt ((1 + x) * (2 + x ^ 3))) MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mono
      · -- Show sqrt f(x) is continuous 
        apply ContinuousOn.sqrt
        all_goals
        try { 
          apply Continuous.continuousOn
          continuity
        }
        try { 
          intro x hx
          simp at hx ⊢ 
          all_goals
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((x : ℝ) + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x ^ 2 - 1)]
        }
        try { 
          simp 
        }
        all_goals 
        try { positivity }
        try { norm_num [mul_pos] }
        <;> try { linarith }
        all_goals try tauto 
      · -- Show the image is in the required subset
        intro x hx
        simp at hx ⊢ 
        all_goals 
        have hx1 : 0 ≤ x := by
          nlinarith
        have hx2 : x ≤ 1 := by 
          nlinarith
        apply h1 x hx1 hx2
    have hg : IntervalIntegrable (fun x : ℝ => x + 3 / 2) MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
      apply Continuous.intervalIntegrable
      continuity
    have h3 : ∀ x, x ∈ Set.Icc (0 : ℝ) (1 : ℝ) → sqrt ((1 + x) * (2 + x ^ 3)) ≤ (x + 3 / 2 : ℝ) := by 
      intro x hx
      have hx1 : 0 ≤ x := by 
        have h := hx.1
        nlinarith
      have hx2 : x ≤ 1 := by 
        have h := hx.2
        nlinarith
      apply h1 x hx1 hx2
    apply intervalIntegral.integral_mono_on 
    all_goals 
      try { 
        exact hf 
      }
      try { 
        exact hg 
      }
      try { 
        exact h3 
      }
    all_goals 
      try { 
        tauto 
      }
      try { 
        aesop 
      }
      all_goals try tauto
  have h3 : ∫ x in (0)..1, (x + 3 / 2 : ℝ) = 2 := by 
    norm_num [intervalIntegral.integral_const, add_assoc]
    <;> ring_nf <;> norm_num 
  linarith [h2, h3]
  all_goals try { 
    positivity 
  }
  <;> try { 
    norm_num 
    <;> tauto 
  }