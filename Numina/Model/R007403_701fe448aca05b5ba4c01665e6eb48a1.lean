import Mathlib

theorem number_theory_14989 : {x : ℕ | x ∈ Finset.Icc 100 999 ∧ (3874 * x + 481) ≡ 1205 [MOD 23]}.encard = 40 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 100 999 ∧ (3874 * x + 481) ≡ 1205 [MOD 23]} = Finset.filter (fun x => (3874 * x + 481) ≡ 1205 [MOD 23]) (Finset.Icc 100 999) := by
    ext x
    simp [Nat.ModEq]
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc, Nat.ModEq]
  <;> try { native_decide }