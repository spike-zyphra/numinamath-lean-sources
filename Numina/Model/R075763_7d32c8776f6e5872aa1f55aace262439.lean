import Mathlib

theorem algebra_177360 {a b c : ℝ} (ha : a ≠ -b - c) (hb : b ≠ -a - c)
    (hc : c ≠ -a - b) (h : a = 0.02 ∧ b = -11.05 ∧ c = 1.07) :
    ((1 / a - 1 / (b + c)) / (1 / a + 1 / (b + c))) *
    (1 + (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c)) / ((a - b - c) / (a * b * c)) = 0.1 := by
  rcases h with ⟨ha_eq, hb_eq, hc_eq⟩
  rw [ha_eq, hb_eq, hc_eq]
  norm_num