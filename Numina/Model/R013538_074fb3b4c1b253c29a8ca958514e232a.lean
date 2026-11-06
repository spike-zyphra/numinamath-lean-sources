import Mathlib

open Nat

theorem number_theory_101218 (p : ℕ) (hp : p.Prime) :
    ((p - 1)! : ZMod p) = -1 := by
  have h : Fact p.Prime := ⟨hp⟩
  apply ZMod.wilsons_lemma