import Mathlib

theorem number_theory_193287 : {p | Nat.Prime p ∧ ∃ k, p = 4 * k + 3}.Infinite := by
  have : IsUnit (3 : ZMod 4) := by
    rw [isUnit_iff_exists]; use 3; reduce_mod_char
    simp
  replace this := Nat.setOf_prime_and_eq_mod_infinite this
  convert this with p; rw [ZMod.natCast_eq_iff]
  rw [show ZMod.val 3 = 3 by rfl]; simp [add_comm]
