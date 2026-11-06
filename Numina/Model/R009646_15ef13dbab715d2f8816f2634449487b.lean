import Mathlib

theorem Nat.mul_add_mod_self_left : ∀ (a b c : ℕ), (a * b + c) % a = c % a :=
fun a b c =>
  Eq.mpr (id (congrArg (fun _a => _a % a = c % a) (Nat.add_comm (a * b) c)))
    (Eq.mpr (id (congrArg (fun _a => _a = c % a) (Nat.add_mul_mod_self_left c a b))) (Eq.refl (c % a)))

open Finset

theorem number_theory_611049 : #{n ∈ Icc 1 100 | Odd (∑ i ∈ Icc 1 n, n / i)} = 55 := by 
  native_decide