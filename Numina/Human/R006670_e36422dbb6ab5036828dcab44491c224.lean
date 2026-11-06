import Mathlib

/-
Let $k$ be a non-negative integer. Consider the set of nine consecutive integers $S_k = \{k+1, k+2, \ldots, k+9\}$.
Let an arrangement $a_k$ of these numbers in a circle be $(k+3, k+1, k+7, k+4, k+9, k+2, k+6, k+5, k+8)$, where $k+8$ is adjacent to $k+3$.
Theorem: For $k=15$, the arrangement $a_k$ has the property that the sum of any two adjacent numbers in $a_k$ is not divisible by $3$, not divisible by $5$, and not divisible by $7$.
 -/
namespace number_theory_639905

def S (k : ℕ) : Finset ℕ := Finset.Icc (k + 1) (k + 9)

def a (k : ℕ) : Fin 9 → ℕ := ![k + 3, k + 1, k + 7, k + 4, k + 9, k + 2, k + 6, k + 5, k + 8]

theorem number_theory_639905 (k : ℕ) (hk : k = 15) :
    ∀ i, let s := a k i + a k (i + 1); ¬ 3 ∣ s ∧ ¬ 5 ∣ s ∧ ¬ 7 ∣ s := by
  subst hk
  decide
end number_theory_639905
open number_theory_639905
