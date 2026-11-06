import Mathlib

open Real
open scoped BigOperators

theorem inequalities_29063 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  (2*a*(2*a - (a+b+c)/2))/(b+c) + (2*b*(2*b - (a+b+c)/2))/(c+a) +
  (2*c*(2*c - (a+b+c)/2))/(a+b) ≥ (a+b+c)/2 := by
  have hb' : 0 < b := hb
  have hc' : 0 < c := hc
  have ha' : 0 < a := ha
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : b + c > 0 := by linarith
  have h5 : c + a > 0 := by linarith
  have h6 : a + b > 0 := by linarith
  have h7 : (2*a*(2*a - (a+b+c)/2))/(b+c) + (2*b*(2*b - (a+b+c)/2))/(c+a) +
    (2*c*(2*c - (a+b+c)/2))/(a+b) - (a+b+c)/2 ≥ 0 := by
    have pos1 : b + c > 0 := by linarith
    have pos2 : c + a > 0 := by linarith
    have pos3 : a + b > 0 := by linarith
    have h8 : (2*a*(2*a - (a+b+c)/2))/(b+c) + (2*b*(2*b - (a+b+c)/2))/(c+a) +
      (2*c*(2*c - (a+b+c)/2))/(a+b) - (a+b+c)/2 =
      ( a*(3*a - b - c)*(c + a)*(a + b) +
        b*(3*b - c - a)*(b + c)*(a + b) +
        c*(3*c - a - b)*(b + c)*(c + a) - (a + b + c)/2 * (b + c)*(c + a)*(a + b) ) / ( (b + c) * (c + a) * (a + b) ) := by 
      field_simp
      ring_nf
    rw [h8] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a*(a - b)), sq_nonneg (a*(a - c)), sq_nonneg (a*(b - c)),
      sq_nonneg (b*(a - b)), sq_nonneg (b*(a - c)), sq_nonneg (b*(b - c)),
      sq_nonneg (c*(a - b)), sq_nonneg (c*(a - c)), sq_nonneg (c*(b - c)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), -- (a + b - c) * (a + c - b)
      mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), -- (a + c - b) * (b + c - a)
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h'') -- (a + b - c) * (b + c - a)
    ]
    positivity
  linarith