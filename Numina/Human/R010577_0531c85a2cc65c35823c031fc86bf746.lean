import Mathlib

/- Bob is visiting Japan and he wants to buy a coffee for $200$ yen. If one U.S. dollar is worth $108$ yen, how much money, in USD to the nearest hundredth, does he have to spend for the coffee? (You may use a calculator on this problem.) -/
theorem algebra_13757 {x : ℝ} (hx : x * 108 = 200) : ⌊x * 100 + 1 / 2⌋ / 100 = (1.85 : ℝ) := by
  replace hx : x = (200 / 108 : ℝ) := by
    linarith only [hx]
  rw [hx]
  norm_num
