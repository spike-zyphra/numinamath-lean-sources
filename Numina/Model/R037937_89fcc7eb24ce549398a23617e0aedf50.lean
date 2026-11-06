import Mathlib

open Real
open scoped BigOperators

theorem inequalities_603735 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (s : ℝ) (hs : s = (a + b + c) / 2)
  (Δ : ℝ) (hΔ : Δ = (1 / 2) * a * b * sin (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b))))
  :
  (s - a) ^ 4 + (s - b) ^ 4 + (s - c) ^ 4 ≥ Δ ^ 2 := by

  have h1 : -1 ≤ (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) := by
    have hc1 : a + b > c := by linarith
    have ha1 : a + c > b := by linarith
    have hb1 : b + c > a := by linarith
    have h7 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≥ -1 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
    linarith

  have h1' : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤ 1 := by
    have hc1 : a + b > c := by linarith
    have ha1 : a + c > b := by linarith
    have hb1 : b + c > a := by linarith
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]

  have h1'' : ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ^ 2 ≤ 1 := by 
    nlinarith [h1, h1']

  have h15 : Δ ^ 2 = s * (s - a) * (s - b) * (s - c) := by
    rw [hΔ]
    have h6 : ((1 / 2) * a * b * sin (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)))) ^ 2 =
          (1 / 4) * a ^ 2 * b ^ 2 * (1 - ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ^ 2) := by
      have h20 : sin (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ) ^ 2 = 1 - ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ^ 2 := by
        have h40 : sin (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ) ^ 2 = 1 - cos (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ) ^ 2 := by
          rw [sin_sq]
        have h41 : cos (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ) = (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) := by
          apply Real.cos_arccos
          all_goals
          nlinarith [show a * b > 0 by positivity, show -1 ≤ (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) by linarith [h1], show (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤ 1 by linarith [h1']]
        rw [h41] at h40
        linarith

      calc
        ((1 / 2) * a * b * sin (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)))) ^ 2
          = (1 / 4) * a ^ 2 * b ^ 2 * (sin (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ) ^ 2) := by 
            ring
        _ = (1 / 4) * a ^ 2 * b ^ 2 * (1 - ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ^ 2) := by 
          rw [h20]

    have h7 : s * (s - a) * (s - b) * (s - c) = (1 / 16) * ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)) := by
      rw [hs]
      ring

    have h8 : (1 / 4) * a ^ 2 * b ^ 2 * (1 - ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ^ 2) =
        s * (s - a) * (s - b) * (s - c) := by
      rw [h7]
      field_simp
      ring_nf

    linarith [h6, h8]

  have h19 : (s - a) ^ 4 + (s - b) ^ 4 + (s - c) ^ 4 ≥ s * (s - a) * (s - b) * (s - c) := by
    rw [hs]
    have ha1 : 0 < a := ha
    have hb1 : 0 < b := hb
    have hc1 : 0 < c := hc
    have ha2 : a + b > c := by linarith
    have hb2 : a + c > b := by linarith
    have hc2 : b + c > a := by linarith
    nlinarith [sq_nonneg (( (a + b + c) / 2 - a ) ^ 2 - ( (a + b + c) / 2 - b ) ^ 2 ), sq_nonneg ( ( (a + b + c) / 2 - a ) ^ 2 - ( (a + b + c) / 2 - c ) ^ 2 ), sq_nonneg ( ( (a + b + c) / 2 - b ) ^ 2 - ( (a + b + c) / 2 - c ) ^ 2 ), 
      sq_nonneg ( ( (a + b + c) / 2 - a ) - ( (a + b + c) / 2 - b ) ), sq_nonneg ( ( (a + b + c) / 2 - a ) - ( (a + b + c) / 2 - c ) ), sq_nonneg ( ( (a + b + c) / 2 - b ) - ( (a + b + c) / 2 - c ) ), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < (a + b - c) by linarith) (show 0 < (a + c - b) by linarith), 
      mul_pos (show 0 < (a + c - b) by linarith) (show 0 < (b + c - a) by linarith), 
      mul_pos (show 0 < (a + b - c) by linarith) (show 0 < (b + c - a) by linarith) ]
  
  nlinarith [h15, h19]