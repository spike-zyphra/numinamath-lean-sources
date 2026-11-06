import Mathlib

/- We define a predicate for a set to be a K-solution. -/
def is_K_solution (K : ℕ) (S : Finset ℕ) : Prop :=
    K > 0 ∧ S.card = 4 ∧ ∀ m ∈ S, ∀ n ∈ S, m ≠ n → Nat.Prime (m * n + K * ∏ i ∈ S \ {m, n}, i)

/- Let $K$ be a positive natural number. A set $S=\{a,b,c,d\}$ of four distinct natural numbers is called a $K$-solution if for any two distinct elements $m, n \in S$, the number $m \cdot n + K \cdot (\prod_{i \in S \setminus \{m,n\}} i)$ is prime. Show that for $K=1$, the set $\{1,2,3,5\}$ is a $1$-solution. -/
theorem number_theory_634662 :
    is_K_solution 1 {1, 2, 3, 5} := by
  simp only [is_K_solution]
  -- We check using definition.
  native_decide