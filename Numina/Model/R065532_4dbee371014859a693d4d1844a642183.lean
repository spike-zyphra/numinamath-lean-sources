import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_61321 {Tmax m L0 R v0 : ℝ}
  (hTmax : Tmax > 0) (hm : m > 0) (hL0 : L0 > 0)
  (hR : R > 0) (hv0 : v0 > 0) :
  let L := L0 - m * v0 ^ 2 / (2 * Tmax)
  L = L0 - m * v0 ^ 2 / (2 * Tmax) := by
  intro L
  rfl