import Mathlib

/-
Problem: Determine the number of subsets $S$ of $\{1,2,3, \ldots, 10\}$ with the following property:
there exist integers $a < b < c$ with $a \in S, b \notin S, c \in S$.

Answer: 968. -/
theorem combinatorics_610964 :
    let subsets_with_pattern : Finset (Finset ℕ) := (Finset.powerset (Finset.range 10)).filter 
        (fun S ↦ ∃ (a b c : Fin 10), a < b ∧ b < c ∧ a.val ∈ S ∧ b.val ∉ S ∧ c.val ∈ S)
    subsets_with_pattern.card = 968 :=
  by
  intro _
  native_decide
