import Mathlib

/- How many numbers are in the list $ 4, 6, 8, \ldots, 128, 130 ?$ -/
theorem algebra_12912 : {x : ℕ | Even x ∧ x ∈ Finset.Icc 4 130}.encard = 64 := by
  have h1 : {x : ℕ | Even x ∧ x ∈ Finset.Icc 4 130} = Finset.filter (fun x => Even x) (Finset.Icc 4 130) :=
    by ext x; constructor <;> simp (config := { contextual := true }) [Nat.even_iff]
  rw [h1]
  simp [Finset.filter, Finset.Icc, Finset.card]
  rfl