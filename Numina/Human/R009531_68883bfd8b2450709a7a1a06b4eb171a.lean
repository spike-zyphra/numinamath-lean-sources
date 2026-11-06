import Mathlib

abbrev multmod (p : ℤ × ℤ) (x : ℤ) : ℤ := x * p.1 % p.2

abbrev seq_multmod (pl : List (ℤ × ℤ)) (x : ℤ) : ℤ :=
  pl.foldl (fun acc p => multmod p acc) x

/-
Find the sequence obtained by applying successively the modular multiplications with multipliers and moduli $(7,92),(11,95)$, and $(6,101)$, respectively, on the super-increasing sequence $(3,4,8,17,33,67)$.
-/
theorem number_theory_4977 : [3,4,8,17,33,67].map (seq_multmod [(7, 92), (11, 95), (6, 101)])
    = [44, 37, 74, 72, 50, 24] := by
  -- verify by computation
  native_decide
