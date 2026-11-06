import Mathlib

/- An occasionally unreliable professor has devoted his last book to a certain binary operation $*$. When this operation is applied to any two integers, the result is again an integer. The operation is known to satisfy the following axioms:

(a) $x *(x * y)=y$ for all $x, y \in \mathbb{Z}$;

(b) $(x * y) * y=x$ for all $x, y \in \mathbb{Z}$.

The professor claims in his book that

(C1) the operation $*$ is commutative: $x * y=y * x$ for all $x, y \in \mathbb{Z}$.

(C2) the operation $*$ is associative: $(x * y) * z=x *(y * z)$ for all $x, y, z \in \mathbb{Z}$.

Which of these claims follow from the stated axioms?

Answer: (C1) is true; (C2) is false. -/
theorem algebra_241720 (star : ℤ → ℤ → ℤ)
  (h₁ : ∀ x y : ℤ, star x (x + y) = y)
  (h₂ : ∀ x y : ℤ, star (x + y) y = x) :
  (∀ a b : ℤ, star a b = star b a) ∧
  (∃ a b c : ℤ, star (star a b) c ≠ star a (star b c)) :=
by
  constructor
  -- Prove the first part of the conjunction: ∀ a b : ℤ, star a b = star b a
  . intro a b
    -- Step 1: Use h₂ to express star((a - b) + b) as a - b
    have t1 : star ((a - b) + b) b = a - b := h₂ (a - b) b
    -- Step 2: Use h₁ to express star b (b + (a - b)) as a - b
    have t2 : star b (b + (a - b)) = a - b := h₁ b (a - b)
    -- Step 3: Simplify the equations (a - b) + b = a and b + (a - b) = a using ring arithmetic
    have eq1 : (a - b) + b = a := by ring
    have eq2 : b + (a - b) = a := by ring
    -- Step 4: Apply the simplifications to t1 and t2
    rw [eq1] at t1
    rw [eq2] at t2
    -- Step 5: Final substitution to prove star a b = star b a
    rw [t1, t2]

  -- Prove the second part of the conjunction: ∃ a b c : ℤ, star (star a b) c ≠ star a (star b c)
  · use 1, 2, 3
    -- Step 6: Use specific values for a, b, and c (here we choose 1, 2, and 3)
    -- Step 7: Apply h₁ to evaluate star with specific values
    have h₃ := h₁ 1 1
    have h₄ := h₁ 2 1
    have h₅ := h₁ 1 0
    have h₆ := h₁ 1 2
    -- Step 8: Simplify the results of the h₁ applications
    simp at h₃ h₄ h₅ h₆
    -- Step 9: Perform the necessary substitutions and use linarith to finish the proof
    rw [h₃, h₄, h₅]
    linarith