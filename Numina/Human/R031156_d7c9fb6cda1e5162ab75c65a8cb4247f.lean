import Mathlib

/- Alice wants to buy $3$ pounds of veal at the grocery store, but the scales at the store only show weight in kilograms. If one kilogram is $2.20$ pounds, how many kilograms of veal should Alice buy?  (You may use a calculator on this problem; answer to the nearest hundredth.) -/
theorem algebra_21304 (veal price x : ℝ) (hv : veal = 3) (hp : price = 2.20) (h : x * price = veal) :
    (round (100 * x) : ℝ) / 100 = 1.36 := by
  -- $x = \mathrm{veal} / \mathrm{price}$
  apply eq_div_of_mul_eq at h
  -- $\mathrm{round} (100 \cdot x) = 136$
  have eq : round (100 * x) = 136 := by
    rw [h, hv, hp]
    norm_num
    -- $2 \cdot \mathrm{fract} (1500 / 11) < 1$
    have fraclt : 2 * Int.fract (1500 / 11 : ℝ) < 1 := by
      -- $\mathrm{fract} (1500 / 11) < 1 / 2$
      have lt : Int.fract ((1500 : ℤ) / (11 : ℕ) : ℝ) < 1 / 2 := by
        rw [Int.fract_div_intCast_eq_div_intCast_mod]
        norm_num
      rw [Int.cast_ofNat, Nat.cast_ofNat] at lt
      linarith
    -- suffices to show $\left\lfloor 1500 / 11 \right\rfloor = 136$
    simp [round, fraclt]
    norm_num
  -- so $\mathrm{round} (100 \cdot x) / 100 = 1.36$
  norm_num [eq]
  norm_num [hp]
