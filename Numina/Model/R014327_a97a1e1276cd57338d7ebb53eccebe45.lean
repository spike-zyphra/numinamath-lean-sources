import Mathlib

open Nat

theorem number_theory_156424 (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ((p - 1)! : ZMod p) = -1 := by
  apply ZMod.wilsons_lemma