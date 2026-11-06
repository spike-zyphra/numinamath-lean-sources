import Mathlib

/-
Example 5 (2003 Hunan Province Competition Question) Let $x, y \in \mathbf{R}$, and satisfy
$$
\left\{\begin{array}{l}
(x-1)^{2003}+2002(x-1)=-1, \\
(y-2)^{2003}+2002(y-2)=1 .
\end{array}\right.
$$

Then $x+y=$ $\qquad$
-/
theorem algebra_249253 {x y : ℝ}
    (hx : (x - 1) ^ 2003 + 2002 * (x - 1) = -1) (hy : (y - 2) ^ 2003 + 2002 * (y - 2) = 1) :
    x + y = 3 := by
  -- Construct the function $f(t)=t^{2003}+2002 t$,
  -- It is easy to see that $f(t)$ is an odd function on $\mathbf{R}$ and is also monotonic.
  let f (t : ℝ) := t ^ 2003 + 2002 * t
  have hf : StrictMono f := by
    unfold f
    apply StrictMono.add
    · apply Odd.strictMono_pow
      exact Nat.odd_iff.mpr rfl
    · apply StrictMono.const_mul
      · exact fun ⦃a b⦄ a => a
      · simp
  apply StrictMono.injective at hf
  --  From this, we get $f(x-1)=-f(y-2)$, i.e., $f(x-1)=f(2-y)$.
  have : f (x - 1) = f (2 - y) := by
    unfold f
    rw [hx, ←hy]
    rw [neg_add]
    congr
    · rw [show 2 - y =  - (y - 2) by simp]
      rw [neg_pow]
      norm_num
    · ring
  -- Thus $x-1=2-y$, i.e., $x+y=3$.
  apply hf at this
  linarith only [this]
