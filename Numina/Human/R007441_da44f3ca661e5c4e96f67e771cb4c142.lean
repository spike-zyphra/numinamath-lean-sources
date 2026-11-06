import Mathlib

open Int

-- Theorem: For any integer n, 6 divides n³ - 7n
theorem number_theory_607371 (n : ℤ) : 6 ∣ n^3 - 7 * n := by
  -- Let r be the remainder of n modulo 6, i.e., n ≡ r mod 6 with 0 ≤ r < 6
  let r := n % 6

  -- Establish the congruence n ≡ r mod 6
  have h : ModEq 6 n r := ModEq.symm (Int.mod_modEq _ _)

  -- Use properties of congruences:
  -- If n ≡ r mod 6, then n³ ≡ r³ and 7n ≡ 7r mod 6,
  -- so n³ - 7n ≡ r³ - 7r mod 6
  have mod_eq : n^3 - 7 * n ≡ r^3 - 7 * r [ZMOD 6] :=
    (h.pow 3).sub (h.mul_left 7)

  -- Confirm that r ∈ {0, 1, 2, 3, 4, 5}
  have r_nonneg : 0 ≤ r := Int.emod_nonneg _ (by decide)
  have r_lt : r < 6 := Int.emod_lt _ (by decide)
  have r_range : 0 ≤ r ∧ r < 6 := ⟨r_nonneg, r_lt⟩

  -- Use case analysis on the 6 possible values of r
  interval_cases r

  case «0» =>
    -- r = 0 → r³ - 7r = 0 - 0 = 0 ≡ 0 mod 6
    exact Int.modEq_zero_iff_dvd.mp (mod_eq.trans (ModEq.refl 0))

  case «1» =>
    -- r = 1 → 1³ - 7*1 = -6 ≡ 0 mod 6
    exact Int.modEq_zero_iff_dvd.mp (mod_eq.trans (ModEq.refl (-6)))

  case «2» =>
    -- r = 2 → 8 - 14 = -6 ≡ 0 mod 6
    exact Int.modEq_zero_iff_dvd.mp (mod_eq.trans (ModEq.refl (-6)))

  case «3» =>
    -- r = 3 → 27 - 21 = 6 ≡ 0 mod 6
    exact Int.modEq_zero_iff_dvd.mp (mod_eq.trans (ModEq.refl (6)))

  case «4» =>
    -- r = 4 → 64 - 28 = 36 ≡ 0 mod 6
    exact Int.modEq_zero_iff_dvd.mp (mod_eq.trans (ModEq.refl (36)))

  case «5» =>
    -- r = 5 → 125 - 35 = 90 ≡ 0 mod 6
    exact Int.modEq_zero_iff_dvd.mp (mod_eq.trans (ModEq.refl (90)))
