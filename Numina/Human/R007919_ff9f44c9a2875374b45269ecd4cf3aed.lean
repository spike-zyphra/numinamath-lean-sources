import Mathlib
open InnerProductSpace
/-Find the value of $a$ so that the lines described by

\[\begin{pmatrix} -1 \\ 2 \\ 5 \end{pmatrix} + t \begin{pmatrix} 2 \\ a \\ 4 \end{pmatrix}\]and

\[\begin{pmatrix} -7 \\ -3 \\ 11 \end{pmatrix} + u \begin{pmatrix} -1 \\ 4 \\ 2 \end{pmatrix}\]are perpendicular.-/
theorem calculus_23032 (t u: EuclideanSpace ℝ (Fin 3)) (a : ℝ) (h₀ : t = ![2,a,4]) (h₁ : u = ![-1,4,2])

    (h₂ : ⟪t, u⟫_ℝ = 0) :
    a = -3 / 2 := by
    --The direction vector of the first line is $\begin{pmatrix} 2 \\ a \\ 4 \end{pmatrix}.$  The direction vector of the second line is $\begin{pmatrix} -1 \\ 4 \\ 2 \end{pmatrix}.$
    --Substitute the vector formula and simplify it
    rw [h₀] at h₂; rw [h₁] at h₂; simp at h₂
    rw [Finset.sum] at h₂
    --Since the lines are perpendicular, the direction vectors will be orthogonal, which means their dot product will be 0.
    norm_num at h₂
    --This gives us\[(2)(-1) + (a)(4) + (4)(2) = 0.\]
    ring_nf at h₂
    --Solving, we find $a = \boxed{-\frac{3}{2}}.$
    have e := congrArg ( fun (n) => ((n) - 6) / 4) h₂; beta_reduce at e; ring_nf at e
    exact e
