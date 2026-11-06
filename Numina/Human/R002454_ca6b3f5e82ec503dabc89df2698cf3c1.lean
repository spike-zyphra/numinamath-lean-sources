import Mathlib

/-- The median of the list $n, n + 3, n + 4, n + 5, n + 6, n + 8, n + 10, n + 12, n + 15$ is $10$.
What is the mean?

$\textbf{(A) }4\qquad\textbf{(B) }6\qquad\textbf{(C) }7\qquad\textbf{(D) }10\qquad\textbf{(E) }11$ -/
theorem algebra_93646 (n : ℝ) (a : Fin 9 → ℝ)
    (ha : a = ![n, n + 3, n + 4, n + 5, n + 6, n + 8, n + 10, n + 12, n + 15]) (hmedian : a 4 = 10) :
    (∑ i, a i) / 9 = 11 := by

  -- The median is $n + 6$. This is given as $10$.
  have : n + 6 = 10 := by
    calc _ = a 4 := by rw [ha]; rfl
         _ = _ := by exact hmedian

  -- Therefore, $n = 4$.
  have hn : n = 4 := by
    calc _ = n + 6 - 6 := by exact Eq.symm (add_sub_cancel_right n 6)
         _ = 10 - 6 := by rw [this]
          _ = 4 := by norm_num

  -- The sum of the terms is $9n + 63$.
  have hsum : (∑ i, a i) = 9 * n + 63 := by
    simp [Finset.sum, ha]
    ring

  -- We know that $n = 4$. Therefore, the sum is $9 \times 4 + 63 = 99$.
  replace hsum : ∑ i, a i = 99 := by
    rw [hsum, hn]
    norm_num

  -- The average is the sum divided by $9$ which is $11$.
  rw [hsum]
  norm_num