import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_282995 (a b c : ℝ) (ha : a ∈ Icc (1/2) 1) (hb : b ∈ Icc (1/2) 1)
    (hc : c ∈ Icc (1/2) 1) :
    2 ≤ ((a+b)/(1+c) + (b+c)/(1+a) + (c+a)/(1+b)) ∧
    ((a+b)/(1+c) + (b+c)/(1+a) + (c+a)/(1+b)) ≤ 3 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  constructor
  · -- Prove the lower bound: $s \geq 2$.
    have h1 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≥ 2 := by
      have h2 : 0 < 1 + c := by linarith
      have h3 : 0 < 1 + a := by linarith
      have h4 : 0 < 1 + b := by linarith
      have h5 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 2 ≥ 0 := by
        have h6 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 2 =
            ((a + b) * (1 + a) * (1 + b) + (b + c) * (1 + c) * (1 + b) + (c + a) * (1 + c) * (1 + a) - 2 * (1 + c) * (1 + a) * (1 + b)) / ((1 + c) * (1 + a) * (1 + b)) := by
          field_simp
          ring
        rw [h6] at *
        apply div_nonneg
        nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha2), 
                  mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hb2), 
                  mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hc2), 
                  mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
                  mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith), 
                  mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith), 
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), 
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1), 
                  mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), 
                  mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2), 
                  mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc2), 
                  mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hc2), 
                  mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - b by linarith), 
                  mul_nonneg (show 0 ≤ 1 - b by linarith) (show 0 ≤ 1 - c by linarith), 
                  mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - c by linarith)]
        positivity
      linarith
    linarith
  · -- Prove the upper bound: $s \leq 3$.
    have h2 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≤ 3 := by
      have h2 : 0 < 1 + c := by linarith
      have h3 : 0 < 1 + a := by linarith
      have h4 : 0 < 1 + b := by linarith
      have h5 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 3 ≤ 0 := by
        have h6 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 3 =
            ((a + b) * (1 + a) * (1 + b) + (b + c) * (1 + c) * (1 + b) + (c + a) * (1 + c) * (1 + a) - 3 * (1 + c) * (1 + a) * (1 + b)) / ((1 + c) * (1 + a) * (1 + b)) := by
          field_simp
          ring
        rw [h6] at *
        apply div_nonpos_of_nonpos_of_nonneg
        nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha2), 
                  mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hb2), 
                  mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hc2), 
                  mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
                  mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith), 
                  mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith), 
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), 
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1), 
                  mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), 
                  mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2), 
                  mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc2), 
                  mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hc2), 
                  mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - b by linarith), 
                  mul_nonneg (show 0 ≤ 1 - b by linarith) (show 0 ≤ 1 - c by linarith), 
                  mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - c by linarith)]
        positivity
      linarith
    linarith