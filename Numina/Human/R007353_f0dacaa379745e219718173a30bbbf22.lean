import Mathlib

/- aux function to find the next prime
 The function is terminable as the infinitude of prime numbers -/
abbrev nxt_prime (x : ℕ) : ℕ :=
  have : ∃ p, x < p ∧ Nat.Prime p := Nat.exists_infinite_primes x.succ
  Nat.find this

abbrev find_next_ok_prime (p : ℕ) (max_depth : ℕ) : Option ℕ :=
  if max_depth = 0 then none
  else
    let next := nxt_prime p
    if (2 ^ next - 1).Prime then some next
    else find_next_ok_prime next (max_depth - 1)

abbrev nth_ok_prime (n : ℕ) : Option ℕ :=
  match n with
  | 0 => some 1
  | 1 => some 2
  | n + 1 =>
    match nth_ok_prime n with
    | none => none
    | some prev_prime => find_next_ok_prime prev_prime 100

/- the sequence of perfect number -/
abbrev perfect_number (n : ℕ) : ℕ :=
  match nth_ok_prime n with
  | none => 0
  | some p => (2 ^ (p - 1) * (2 ^ p - 1))

/- Find the six smallest even perfect numbers. -/
theorem number_theorry_4917 : [1, 2, 3, 4, 5, 6].map perfect_number =
    [6, 28, 496, 8128, 33550336, 8589869056] := by
  -- verify by computation
  native_decide
