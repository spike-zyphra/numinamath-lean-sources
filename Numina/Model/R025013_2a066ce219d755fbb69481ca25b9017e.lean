import Mathlib

open Finset Real

theorem algebra_104820 {a : ℕ → ℝ} (ha : ∀ n, a n = a 0 * q ^ n)
    (ha0 : a 0 = 1536) (hq : q = -1 / 2) (Pi : ℕ → ℝ)
    (hPi : ∀ n, Pi n = ∏ i ∈ range n, a i) :
    IsGreatest {Pi 4, Pi 11, Pi 12, Pi 13} (Pi 12) := by
  constructor
  · -- Show that Π 12 is in the set
    simp
  · -- Show that Π 12 is an upper bound
    intro x hx
    simp at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · -- Case x = Pi 4
      norm_num [hPi, ha0, hq, ha, Finset.prod_range_succ]
    · -- Case x = Pi 11
      norm_num [hPi, ha0, hq, ha, Finset.prod_range_succ]
    · -- Case x = Pi 12
      norm_num [hPi, ha0, hq, ha, Finset.prod_range_succ]
    · -- Case x = Pi 13
      norm_num [hPi, ha0, hq, ha, Finset.prod_range_succ]