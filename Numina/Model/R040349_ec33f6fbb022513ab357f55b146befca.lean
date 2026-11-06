import Mathlib

open BigOperators Real

theorem inequalities_37258 (a b c p r : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ha' : b + c > a) (hb' : a + c > b) (hc' : a + b > c)
  (hp : p = (a + b + c) / 2) (hr : r = √((p-a)*(p-b)*(p-c)/p)) :
  1 / (p - a)^2 + 1 / (p - b)^2 + 1 / (p - c)^2 ≥ 1 / r^2 := by
  have hp1 : 0 < p - a := by
    have h1 : b + c > a := ha'
    linarith [hp]

  have hp2 : 0 < p - b := by
    have h2 : a + c > b := hb'
    linarith [hp]

  have hp3 : 0 < p - c := by
    have h3 : a + b > c := hc'
    linarith [hp]

  have hp4 : 0 < p := by
    linarith [hp1, hp2, hp3]

  have hr2 : r^2 = (p - a) * (p - b) * (p - c) / p := by 
    rw [hr]
    have h1 : (p - a) * (p - b) * (p - c) / p ≥ 0 := by
      apply div_nonneg
      · -- Show that (p - a) * (p - b) * (p - c) ≥ 0
        apply mul_nonneg
        · apply mul_nonneg
          · linarith [hp1]
          · linarith [hp2]
        · linarith [hp3]
      · -- Show that p ≥ 0
        linarith [hp4]
    have h2 : √((p - a) * (p - b) * (p - c) / p) ^ 2 = (p - a) * (p - b) * (p - c) / p := by
      rw [Real.sq_sqrt]
      positivity
    linarith
  have h1 : 1 / r^2 = p / ((p - a) * (p - b) * (p - c)) := by
    rw [hr2]
    have h2 : (p - a) * (p - b) * (p - c) > 0 := by
      positivity
    field_simp
    all_goals nlinarith
  rw [h1]
  have h2 : (p - a) * (p - b) * (p - c) > 0 := by
    positivity
  have h3 : (p - a) ^ 2 * (p - b) ^ 2 * (p - c) ^ 2 > 0 := by
    positivity
  have h4 : 1 / (p - a)^2 + 1 / (p - b)^2 + 1 / (p - c)^2 - p / ((p - a) * (p - b) * (p - c)) ≥ 0 := by
    have h5 : 1 / (p - a)^2 + 1 / (p - b)^2 + 1 / (p - c)^2 - p / ((p - a) * (p - b) * (p - c)) =
        ( (p - b)^2 * (p - c)^2 + (p - a)^2 * (p - c)^2 + (p - a)^2 * (p - b)^2 - p * ((p - a) * (p - b) * (p - c)) ) / ( (p - a)^2 * (p - b)^2 * (p - c)^2 ) := by 
      field_simp
      ring
    rw [h5]
    have h6 : (p - b)^2 * (p - c)^2 + (p - a)^2 * (p - c)^2 + (p - a)^2 * (p - b)^2 - p * ((p - a) * (p - b) * (p - c)) ≥ 0 := by
      have h9 : (p - b)^2 * (p - c)^2 + (p - a)^2 * (p - c)^2 + (p - a)^2 * (p - b)^2 ≥ p * ((p - a) * (p - b) * (p - c)) := by
        rw [hp]
        nlinarith [sq_nonneg ( (p - a) * (p - b) - (p - b) * (p - c) ), sq_nonneg ( (p - b) * (p - c) - (p - c) * (p - a) ), sq_nonneg ( (p - c) * (p - a) - (p - a) * (p - b) ), 
          sq_nonneg ( (p - a) - (p - b) ), sq_nonneg ( (p - b) - (p - c) ), sq_nonneg ( (p - c) - (p - a) ), 
          mul_pos hp1 hp2, mul_pos hp2 hp3, mul_pos hp1 hp3, mul_pos (mul_pos hp1 hp2) hp3 ]
      linarith
    have h7 : (p - a)^2 * (p - b)^2 * (p - c)^2 > 0 := by
      positivity
    apply div_nonneg
    linarith
    positivity
  linarith