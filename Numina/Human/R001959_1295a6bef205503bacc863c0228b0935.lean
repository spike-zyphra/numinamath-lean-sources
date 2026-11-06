import Mathlib 


/- A large candle is 119 centimeters tall. It is designed to burn down more quickly when it is first lit and more slowly as it approaches its bottom. Specifically, the candle takes 10 seconds to burn down the first centimeter from the top, 20 seconds to burn down the second centimeter, and 10k seconds to burn down the k-th centimeter. Suppose it takes T seconds for the candle to burn down completely. Then $T/2$ seconds after it is lit, the candle's height in centimeters will be h. Find $10h$. -/
open BigOperators
open Algebra

theorem algebra_48662 (T : ℝ) (h : ℕ) (hTpos : T > 0) (hhrange : 0 < h ∧ h ≤ 119) (t : ℝ → ℝ) (ht : ∀ k, t k = 10 * k * (k + 1)/2) (hT : T = t 119) (hh : T/2 = t (119 - h)) : 10 * h = 350 := by
  --We compute the total time $T$.
  have hT' : T = 71400 := by
    rw [hT, ht]
    norm_num
  --We subsitute T in hh.
  rw [hT', ht, (by linarith : (71400 : ℝ) = 10 * 7140), mul_assoc] at hh
  field_simp at hh
  symm at hh
  rw [← sub_eq_zero] at hh
  ring_nf at hh
--We can now solve the quadratic equation.
  have : (7140 : ℝ) - (h : ℝ) * (239 : ℝ) + (h : ℝ) ^ 2 = ((h : ℝ) - 204) * (h - 35) := by
    ring_nf
  have : h = 35 := by
    rw [this, mul_eq_zero] at hh
    rcases hh with hh1 | hh2
    · exfalso
      have : h = 204 := by
        rw [sub_eq_zero] at hh1
        exact_mod_cast hh1
      linarith
    · rw [sub_eq_zero] at hh2
      exact_mod_cast hh2
  linarith