import Mathlib

open Classical in
theorem number_theory_10952 (Abundant : ℕ+ → Prop) (abundant_def : ∀ n, Abundant n ↔
    n.val < ∑ d ∈ n.val.properDivisors, d) :
    ((Finset.Ico 1 25).filter Abundant).card = 4 := by

  have h1 : ((Finset.Ico 1 25).filter Abundant) = Finset.filter (fun x => x.val < ∑ d ∈ x.val.properDivisors, d) (Finset.Ico 1 25) := by
    congr
    funext n
    have h2 : Abundant n ↔ n.val < ∑ d ∈ n.val.properDivisors, d := abundant_def n
    simp [h2]

  rw [h1]
  rw [Finset.filter]
  simp [abundant_def]
  <;> native_decide