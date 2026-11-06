import Mathlib

/- Gary purchased a large beverage, but only drank m/n of it, where
m and n are relatively prime positive integers. If he had purchased half
as much and drunk twice as much, he would have wasted only 2/9 as much
beverage. Find m+n -/

theorem algebra_94902 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
(hmn : Nat.Coprime m n) (h :(1/2 - 2 * m / n) = (2 / 9 : ℝ) * (1 - m / n)) :
m + n = 37 := by
  -- simplify to solve the equation for m/n
  apply congr_arg (fun x => x * 18) at h
  ring_nf at h
  apply congr_arg (fun x =>-(x - (9-m * (n:ℝ)⁻¹*4))/32) at h
  ring_nf at h
  rw [inv_eq_one_div, ← mul_div_assoc, mul_one] at h
  -- now just sum the numerator and denominator
  linarith [@Rat.div_int_inj m n 5 32 (by simpa) (by norm_num) (by simpa) (by norm_num) (by rify; linarith)]