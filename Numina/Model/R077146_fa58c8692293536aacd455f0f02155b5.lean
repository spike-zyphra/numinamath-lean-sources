import Mathlib

open Real
open scoped BigOperators

theorem inequalities_982 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (x : ℝ) (hx : 0 ≤ x) :
  (a * x + b)^2 / ((b + c - a) * x + c + a - b) +
  (b * x + c)^2 / ((a + c - b) * x + b + a - c) +
  (c * x + a)^2 / ((a + b - c) * x + b + c - a) ≥
  ((a + b + c) * (x + 1)) / 2 := by
  have pos1 : (b + c - a) * x + c + a - b > 0 := by
    nlinarith [show b + c - a > 0 by linarith, show c + a - b > 0 by linarith, hx]
  have pos2 : (a + c - b) * x + b + a - c > 0 := by
    nlinarith [show a + c - b > 0 by linarith, show b + a - c > 0 by linarith, hx]
  have pos3 : (a + b - c) * x + b + c - a > 0 := by
    nlinarith [show a + b - c > 0 by linarith, show b + c - a > 0 by linarith, hx]
  have h1 : (a * x + b)^2 / ((b + c - a) * x + c + a - b) +
    (b * x + c)^2 / ((a + c - b) * x + b + a - c) +
    (c * x + a)^2 / ((a + b - c) * x + b + c - a) - ((a + b + c) * (x + 1)) / 2 ≥ 0 := by
    have h3 : (a * x + b)^2 / ((b + c - a) * x + c + a - b) +
      (b * x + c)^2 / ((a + c - b) * x + b + a - c) +
      (c * x + a)^2 / ((a + b - c) * x + b + c - a) - ((a + b + c) * (x + 1)) / 2 =
      ((a * x + b)^2 * ((a + c - b) * x + b + a - c) * ((a + b - c) * x + b + c - a) +
        (b * x + c)^2 * ((b + c - a) * x + c + a - b) * ((a + b - c) * x + b + c - a) +
        (c * x + a)^2 * ((b + c - a) * x + c + a - b) * ((a + c - b) * x + b + a - c) -
        ((a + b + c) * (x + 1)) / 2 * ((b + c - a) * x + c + a - b) * ((a + c - b) * x + b + a - c) * ((a + b - c) * x + b + c - a)) /
      (( (b + c - a) * x + c + a - b ) * ( (a + c - b) * x + b + a - c ) * ( (a + b - c) * x + b + c - a ) ) := by
      field_simp [pos1, pos2, pos3]
      <;> ring
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a * x + b - b * x - c), sq_nonneg (b * x + c - c * x - a), sq_nonneg (c * x + a - a * x - b), 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc,
      mul_pos (show 0 < (b + c - a) * x + c + a - b by linarith [show b + c - a > 0 by linarith, show c + a - b > 0 by linarith, hx]) (show 0 < (a + c - b) * x + b + a - c by linarith [show a + c - b > 0 by linarith, show b + a - c > 0 by linarith, hx]), 
      mul_pos (show 0 < (a + c - b) * x + b + a - c by linarith [show a + c - b > 0 by linarith, show b + a - c > 0 by linarith, hx]) (show 0 < (a + b - c) * x + b + c - a by linarith [show a + b - c > 0 by linarith, show b + c - a > 0 by linarith, hx]), 
      mul_pos (show 0 < (b + c - a) * x + c + a - b by linarith [show b + c - a > 0 by linarith, show c + a - b > 0 by linarith, hx]) (show 0 < (a + b - c) * x + b + c - a by linarith [show a + b - c > 0 by linarith, show b + c - a > 0 by linarith, hx])
     ]
    positivity
  linarith