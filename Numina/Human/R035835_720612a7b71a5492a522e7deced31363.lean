import Mathlib

/-
Problem:

Given that \(f(x)= \begin{cases} 2^{x}-3 & ,x > 0\\ g(x) & ,x < 0 \end{cases}\) is an odd function, find the value of \(f(g(-2))\).
-/

/-
Solution

Since \(f(x)\) is an odd function, it has the property \(f(-x)=-f(x)\). Therefore, we can derive the expression for \(g(x)\) when \(x<0\), using the definition of an odd function.

For \(x<0\), we have:
\(f(x) = g(x)\)

However, due to the odd function property:
\(f(-x) = -f(x)\)

By substituting \(x\) with \(-x\) we get:
\(f(-x) = g(-x)\)
\(-f(x) = -g(x)\)

Combining the two expressions for \(f(x)\) and \(f(-x)\) for \(x<0\):
\(f(x) = -f(-x)\)
\(g(x) = -g(-x)\)

This implies that:
\(g(-x) = -g(x)\)

Therefore, the function \(g(x)\) should also be an odd function, and we can write:
\(g(x) = -(-2^{x} + 3)\) for \(x<0\)

Now, we need to evaluate \(f(g(-2))\). Since \(-2<0\), we can calculate \(g(-2)\) using the derived expression:
\(g(-2) = -(-2^{-2} + 3)\)
\(g(-2) = -( -\frac{1}{2^{-2}} + 3)\)
\(g(-2) = -(\frac{1}{4} - 3)\)
\(g(-2) = -(-\frac{11}{4})\)
\(g(-2) = \frac{11}{4}\)

Since \(g(-2) > 0\), we use the definition of \(f(x)\) for \(x>0\) to find:
\(f(g(-2)) = f\left(\frac{11}{4}\right)\)
\(f(g(-2)) = 2^{\frac{11}{4}} - 3\)

Without a numerical answer given, we stop at this point as the result should be a numerical value. However, the answer options are listed as fractions or simple integers, indicating there might be a simpler form or an error in our calculations.

Revisiting the calculation of \(g(-2)\), we must take into account \(g(x)\) is an odd function:
\(g(-2) = -g(2)\)

Since \(g(x)\) for \(x<0\) gives us the opposite sign of \(g(x)\) for \(x>0\), and given \(g(x) = -2^{x} + 3\) for \(x>0\), we correct the calculation of \(g(-2)\) to be:
\(g(-2) = -(-2^{-2} + 3)\)
\(g(-2) = -\left(-\frac{1}{4} + 3\right)\)
\(g(-2) = -\left(-\frac{1}{4} - \frac{12}{4}\right)\)
\(g(-2) = -\left(-\frac{13}{4}\right)\)
\(g(-2) = \frac{13}{4}\)

Again, we realize the given value still does not align with the provided answer choices, which indicates there might be a mistake in our understanding of the problem or translation.

Given that the correct answers are much simpler, let's revise our understanding of \(g(x)\) under \(x < 0\), considering that \(f(x)\) is odd:

For \(x < 0\), \(g(x) = -f(-x)\)
Given \(f(x)\) for \(x > 0\) is \(2^x - 3\), we get:
\(g(x) = -(-2^{-x} + 3)\)

Thus:
\(g(-2) = -(-2^2 + 3)\)
\(g(-2) = -(-4 + 3)\)
\(g(-2) = -(-1)\)
\(g(-2) = 1\)

Now that we have \(g(-2) = 1\), and since \(1 > 0\), we find \(f(g(-2))\) as:
\(f(g(-2)) = f(1)\)
Using the expression for \(f(x)\) for \(x > 0\):
\(f(1) = 2^1 - 3\)
\(f(1) = 2 - 3\)
\(f(1) = -1\)

Now we have a solution that matches one of the given options, indicating a likely correct answer:
\[\boxed{f(g(-2)) = -1}\]

-/

theorem algebra_9269 {f g : ℝ → ℝ} (hf : ∀ x, x > 0 → f x = 2 ^ x - 3)
    (hg : ∀ x, x < 0 → f x = g x) (hodd : ∀ x, - f (-x) = (f x)) :
    f (g (-2)) = 1 := by
      -- obtain the formula of $g$, i.e. $g(x) = 3 - 2^(-x)$ for all $x < 0$.
      have oddg : ∀ x < 0, g (x) = 3 - 2 ^ (-x) := by
        intro x xle0
        rw [← hg x]
        pick_goal 2
        · exact xle0
        · rw [← hodd x]
          have nxge0 : - x > 0 := by exact Left.neg_pos_iff.mpr xle0
          rw [hf (-x)]
          pick_goal 2
          · exact nxge0
          · ring
      -- calculate $g$
      obtain geq : g (-2) = 3 - 2 ^ (- (-(2 : ℝ))) := by
        apply oddg
        norm_cast
      rw [geq]
      simp only [neg_neg, Real.rpow_two]
      -- type coercion
      norm_cast
      simp only [Nat.reducePow, Int.cast_subNatNat, Nat.cast_ofNat, Int.reduceNegSucc, Int.cast_neg,
        Int.cast_one]
      -- calculation in $\Z$
      have : (3 : ℝ) - (4 : ℝ) = -1 := by
        norm_cast
      rw [this]
      rw [hg (-1)]
      pick_goal 2
      · linarith
      · rw [oddg (-(1 : ℝ))]
        pick_goal 2
        · linarith
        · simp only [neg_neg, Real.rpow_one]
          norm_cast