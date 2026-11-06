import Mathlib

open Real

lemma lemma_2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (r : ℝ) (hr : 0 < r) :
    ((a ^ ((1 : ℝ) / 2 + r) + b ^ ((1 : ℝ) / 2 + r)) /
     (a ^ ((1 : ℝ) / 2 - r) + b ^ ((1 : ℝ) / 2 - r))) ≥ (a * b) ^ r := by

  have hpos : 0 < a ^ ((1 : ℝ) / 2 - r) + b ^ ((1 : ℝ) / 2 - r) := by positivity
  have h2 : a ^ ((1 : ℝ) / 2 + r) + b ^ ((1 : ℝ) / 2 + r) ≥ (a * b) ^ r * (a ^ ((1 : ℝ) / 2 - r) + b ^ ((1 : ℝ) / 2 - r)) := by
    have h4 : a ^ ((1 : ℝ) / 2 + r) + b ^ ((1 : ℝ) / 2 + r) =
        a ^ ((1 : ℝ) / 2) * a ^ r + b ^ ((1 : ℝ) / 2) * b ^ r := by
      have h10 : a ^ ((1 : ℝ) / 2 + r) = a ^ ((1 : ℝ) / 2) * a ^ r := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals try linarith
      have h11 : b ^ ((1 : ℝ) / 2 + r) = b ^ ((1 : ℝ) / 2) * b ^ r := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals try linarith
      rw [h10, h11]
      all_goals linarith
    have h5 : ((a * b) ^ r * (a ^ ((1 : ℝ) / 2 - r) + b ^ ((1 : ℝ) / 2 - r))) =
        a ^ ((1 : ℝ) / 2) * b ^ r + b ^ ((1 : ℝ) / 2) * a ^ r := by
      have h6 : (a * b) ^ r = a ^ r * b ^ r := by
        rw [Real.mul_rpow]
        all_goals linarith
      have h7 : a ^ r * b ^ r * (a ^ ((1 : ℝ) / 2 - r) + b ^ ((1 : ℝ) / 2 - r)) =
          a ^ ((1 : ℝ) / 2) * b ^ r + b ^ ((1 : ℝ) / 2) * a ^ r := by
        have h8 : a ^ r * b ^ r * a ^ ((1 : ℝ) / 2 - r) = a ^ ((1 : ℝ) / 2) * b ^ r := by
          have h9 : a ^ r * a ^ ((1 : ℝ) / 2 - r) = a ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_add]
            ring_nf
            all_goals try linarith
          calc
            a ^ r * b ^ r * a ^ ((1 : ℝ) / 2 - r)
              = (a ^ r * a ^ ((1 : ℝ) / 2 - r)) * b ^ r := by ring
            _ = (a ^ ((1 : ℝ) / 2)) * b ^ r := by rw [h9]
            _ = a ^ ((1 : ℝ) / 2) * b ^ r := by ring
        have h9 : a ^ r * b ^ r * b ^ ((1 : ℝ) / 2 - r) = b ^ ((1 : ℝ) / 2) * a ^ r := by
          have h10 : b ^ r * b ^ ((1 : ℝ) / 2 - r) = b ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_add]
            ring_nf
            all_goals try linarith
          calc
            a ^ r * b ^ r * b ^ ((1 : ℝ) / 2 - r)
              = a ^ r * (b ^ r * b ^ ((1 : ℝ) / 2 - r)) := by ring
            _ = a ^ r * (b ^ ((1 : ℝ) / 2)) := by rw [h10]
            _ = a ^ r * b ^ ((1 : ℝ) / 2) := by ring
            _ = b ^ ((1 : ℝ) / 2) * a ^ r := by ring
        linarith [h8, h9]
      rw [h6, h7]
    rw [h4, h5]
    have h14 : (a ^ ((1 : ℝ) / 2) - b ^ ((1 : ℝ) / 2)) * (a ^ r - b ^ r) ≥ 0 := by
      by_cases h' : a ≥ b
      ·
        have h61 : a ^ ((1 : ℝ) / 2) ≥ b ^ ((1 : ℝ) / 2) := by
          apply Real.rpow_le_rpow
          .
            linarith
          .
            linarith
          .
            linarith
        have h62 : a ^ r ≥ b ^ r := by
          apply Real.rpow_le_rpow
          all_goals linarith
        nlinarith
      ·
        push_neg at h'
        have h61 : a ^ ((1 : ℝ) / 2) < b ^ ((1 : ℝ) / 2) := by
          apply Real.rpow_lt_rpow
          all_goals linarith
        have h63 : (a ^ ((1 : ℝ) / 2) - b ^ ((1 : ℝ) / 2)) < 0 := by nlinarith
        have h64 : a ^ r < b ^ r := by
          apply Real.rpow_lt_rpow
          all_goals linarith
        have h65 : (a ^ r - b ^ r) < 0 := by nlinarith
        nlinarith
    linarith [h14]
  apply (le_div_iff₀ hpos).mpr
  linarith [h2]



theorem inequalities_249244 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℝ → ℝ) (hf : f = fun r => (a ^ ((1 / 2) + r) + b ^ ((1 / 2) + r)) /
    (a ^ ((1 / 2) - r) + b ^ ((1 / 2) - r))) :
    ∀ r, 0 < r → f r ≥ (a * b) ^ r := by
  intro r hr
  have h7 : f r = ((a ^ ((1 : ℝ) / 2 + r) + b ^ ((1 : ℝ) / 2 + r)) /
                (a ^ ((1 : ℝ) / 2 - r) + b ^ ((1 : ℝ) / 2 - r))) := by
    rw [hf]
    all_goals norm_num
    <;> ring
  rw [h7]
  apply lemma_2 a b ha hb r hr