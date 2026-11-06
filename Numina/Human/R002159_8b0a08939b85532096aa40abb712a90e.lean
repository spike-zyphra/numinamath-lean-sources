import Mathlib

set_option maxHeartbeats 1000000

def isGuanaco (n : ℕ) : Prop :=
  n ∈ Finset.Icc 1000 9999 ∧ (n / 100) * (n % 100) ∣ n

/- A four-digit number $n=\overline{a b c d}$, where $a, b, c$ and $d$ are digits, with $a \neq 0$, is said to be [i]guanaco[/i] if the product $\overline{a b} \times \overline{c d}$ is a positive divisor of $n$. Find all guanaco numbers.  -/
theorem number_theory_69704 :
  {n | isGuanaco n} = {1352, 1734} := by

  ext n
  unfold isGuanaco
  simp
  constructor
  . intro ⟨⟨h1, h2⟩, h3⟩
    contrapose h3
    interval_cases n
    all_goals try decide
    all_goals simp at h3

  . rintro (rfl | rfl)
    all_goals simp; decide
