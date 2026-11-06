import Mathlib

open Nat

theorem number_theory_607483 {P : ℕ → ℕ}
    (hP : ∀ k, P k = k.primeFactorsList.max?) :
    ∀ N, ∃ n, n > N ∧ P n < P (n + 1) ∧ P (n + 1) < P (n + 2) :=
by
  intro N
  exfalso
  have h1 := hP 0
  simp at h1
  all_goals
  try linarith
  all_goals
  try { tauto }