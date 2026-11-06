import Mathlib

/-
Problem 2. A set $M$ of integers has the properties:
i) 1 is an element of $M$;

ii) if $x$ and $y$ are elements of $M$, then $2x + 3y$ is an element of $M$;

iii) if $x, y$ are integers and $4x - 3y$ is an element of $M$, then $x \cdot y$ is an element of $M$.

Show that the set $M$ contains the numbers $2, 3, 4, 5$ and 2019.
 -/
theorem number_theory_118292 (M : Set ℤ)
    (h1 : (1 : ℤ) ∈ M)
    (h2 : ∀ x ∈ M, ∀ y ∈ M, (2 * x + 3 * y) ∈ M)
    (h3 : ∀ x y : ℤ, (4 * x - 3 * y) ∈ M → (x * y) ∈ M) :
    {2, 3, 4, 5, 2019} ⊆ M := by
  -- Solution. From i) and ii) it follows that $5=2 \cdot 1+3 \cdot 1 \in M$ $1 p$
  have : 5 ∈ M :=
    h2 1 h1 1 h1
  -- From iii) and $5=4 \cdot 2-3 \cdot 1 \in M$ it follows that $2 \cdot 1=2 \in M$ $1 p$
  have : 2 ∈ M :=
    h3 2 1 this
  -- From iii) and $2=4 \cdot 2-3 \cdot 2 \in M$ it follows that $2 \cdot 2=4 \in M$ $1 p$
  have : 4 ∈ M :=
    h3 2 2 this
  -- From iii) and $4=4 \cdot 1-3 \cdot 0 \in M$ it follows that $1 \cdot 0=0 \in M$. Using ii) now we obtain $3=2 \cdot 0+3 \cdot 1 \in M$ $1 p$
  have : 0 ∈ M :=
    h3 1 0 this
  have : 3 ∈ M :=
    h2 0 this 1 h1
  -- For the last requirement, since $2019=2 \cdot 0+3 \cdot 673$, it is sufficient to show that $673 \in M$. Then, from $673=2 \cdot 2+3 \cdot 223,223=2 \cdot 2+3 \cdot 73,73=2 \cdot 2+3 \cdot 23$, we deduce that it is sufficient to show that $23 \in M$. Since $23=2 \cdot 4+3 \cdot 5$ and $4,5 \in M$, the problem is solved $3 p$
  have : 2019 ∈ M := by
    suffices 673 ∈ M by
      exact h2 0 (by assumption) 673 this
    suffices 223 ∈ M by
      exact h2 2 (by assumption) 223 this
    suffices 73 ∈ M by
      exact h2 2 (by assumption) 73 this
    suffices 23 ∈ M by
      exact h2 2 (by assumption) 23 this
    exact h2 4 (by assumption) 5 (by assumption)
  intro n n_in
  rw [show ({2, 3, 4, 5, 2019} : Set ℤ) = ({2, 3, 4, 5, 2019} : Finset ℤ) by simp] at n_in
  norm_cast at n_in
  fin_cases n_in <;>
  . assumption
