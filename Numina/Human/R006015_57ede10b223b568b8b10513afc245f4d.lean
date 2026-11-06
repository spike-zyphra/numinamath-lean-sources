import Mathlib

open Nat

/- 10 people are playing musical chairs with $n$ chairs in a circle. They can be seated in 7 ! ways (assuming only one person fits on each chair, of course), where different arrangements of the same people on chairs, even rotations, are considered different. Find $n$. -/
theorem combinatorics_611114 (n : ℕ) (h : Fintype.card (Fin n ↪ Fin 10) = 7!) : n = 4 := by
  -- "10 people sitting in `n` chairs" becomes a type `Fin n ↪ Fin 10` describing which person
  -- occupies which chair; obviously one person cannot sit in two chairs,
  -- hence the `↪` signifying an injection. The cardinality of this type is `7!`
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin] at h
  -- We first put an upper bound on `n`, because if `n > 10` the `descFactorial` is zero
  have n_le_10 : n ≤ 10 := by
    by_contra! h'; rw [descFactorial_eq_zero_iff_lt.mpr h'] at h; norm_num [factorial] at h
  -- The problem now reduces to `(10 - n)! * 7! = 10!`
  have n_eqn := factorial_mul_descFactorial n_le_10
  rw [h] at n_eqn
  -- or `(10 - n)! = 10! / 7! = 6!`, so `n = 4`
  replace n_eqn := Nat.eq_div_of_mul_eq_left (by positivity) n_eqn
  rw [show 10! / 7! = 6! by norm_num [factorial], eq_comm, factorial_inj (by norm_num)] at n_eqn
  omega
