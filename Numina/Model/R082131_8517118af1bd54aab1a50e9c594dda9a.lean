import Mathlib

open Finset

theorem number_theory_187895 {n : ℕ} (hn : n = (2002^2 - 1)) :
    {x | x ≤ n / 2001 ∧ Nat.Coprime x n}.ncard = 1233 := by
  rw [hn]
  have h1 : {x | x ≤ (2002^2 - 1) / 2001 ∧ Nat.Coprime x (2002^2 - 1)} = Finset.filter (fun x => Nat.Coprime x (2002^2 - 1)) (Finset.Iic ((2002^2 - 1) / 2001)) := by
    ext x
    simp
    <;> try trivial
  rw [h1]
  rw [Finset.filter]
  simp [Nat.coprime_iff_gcd_eq_one]
  <;> try native_decide