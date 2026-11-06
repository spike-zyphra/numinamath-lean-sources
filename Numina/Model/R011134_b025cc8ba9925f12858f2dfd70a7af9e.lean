import Mathlib

open Finset


theorem algebra_700 (d: ℕ) (h: d < 10) (n: ℕ)
  (p: HasSum (fun (i:ℕ) => (↑d * 100 + 25 : ℚ) * 10^(-(3: ℤ) * (i + 1))) (n/810)) : n = 750 := by

  have r : HasSum (fun (i:ℕ) => (↑d * 100 + 25 : ℚ) * 10^(-(3: ℤ) * (i + 1))) ((↑d * 100 + 25 : ℚ) / 999) := by
    apply HasSum.mul_left
    conv in 10 ^ (-3 * (↑i + 1)) =>
      tactic =>
        rw [zpow_mul, zpow_add₀, zpow_natCast, zpow_one]
        norm_num
    conv in Rat.inv 999 =>
      tactic =>
        rw [<- mul_one (Rat.inv 999), <- inv_mul_cancel₀ (a := (10^(-3: ℤ) : ℚ)), <- mul_assoc]
        norm_num

    apply HasSum.mul_right
    norm_num

    -- Rewrite the result of the sum so that it is the result of a geometric series.
    have s : ((1 - (1/1000))⁻¹: ℚ) = 1000 / 999 := by norm_num
    rw [mul_comm, <- Rat.div_def, <- s]
    apply hasSum_geometric_of_norm_lt_one (K := ℚ)
    simp [norm,abs]
    norm_num

  have q := HasSum.unique p r
  field_simp at q
  have h1 : (n : ℚ) * 999 = 810 * (100 * (d : ℚ) + 25) := by 
    linarith

  have h2 : n * 999 = 810 * (100 * d + 25) := by
    exact_mod_cast h1

  have h3 : d < 10 := h
  interval_cases d <;> omega