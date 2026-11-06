import Mathlib
open Finset

theorem algebra_171089 :
  let I : Finset _ := {(a, b, c, d) : (ZMod 23) × (ZMod 23) × (ZMod 23) × (ZMod 23) | a + d = 1 ∧ a * d - b * c = 0};
    Finset.card I = 552 := by
  intro I
  native_decide