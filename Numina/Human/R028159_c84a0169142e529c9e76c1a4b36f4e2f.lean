import Mathlib

/- PROBLEM 3. The set $A$ of natural numbers has the properties:

(i) $2 \in A$;

(ii) if $x \in A$, then $4 x \in A$;

(iii) if $9 x+11 \in A$, then $x \in A$.

Show that $13 \in A$. -/
theorem number_theory_111220 (A : Set ℕ) (hA : 2 ∈ A) (hA' : ∀ x ∈ A, 4 * x ∈ A)
    (hA'' : ∀ x, 9 * x + 11 ∈ A → x ∈ A) : 13 ∈ A := by
  -- It suffices to prove that 128 is in A by the third rule.
  suffices 128 ∈ A by
    have exp : 128 = 9 * 13 + 11 := by norm_num
    rw [exp] at this
    apply hA''
    exact this
  -- Use rule 2 three times to prove that 128 is in A.
  have f1 : 8 ∈ A := hA' 2 hA
  have f2 : 32 ∈ A := hA' 8 f1
  have f3 : 128 ∈ A := hA' 32 f2
  exact f3