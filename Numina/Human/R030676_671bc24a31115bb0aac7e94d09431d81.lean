import Mathlib

/-
$r$ and $s$ are integers such that
$$
3 r \geq 2 s-3 \text { and } 4 s \geq r+12 .
$$
What is the smallest possible value of $r / s$ ?
-/
theorem inequalities_611159 :
    IsLeast {k : ℝ | ∃ r s : ℤ, 3 * r ≥ 2 * s - 3 ∧ 4 * s ≥ r + 12 ∧ k = r / s} (1 / 2) := by
  constructor
  -- We find that this point is $(2,4)$, as circled in the figure, so the answer is $2 / 4=1 / 2$.
  · simp
    use 2, 4
    norm_num
  · simp only [lowerBounds, ge_iff_le, tsub_le_iff_right, Set.mem_setOf_eq, forall_exists_index,
    and_imp]
    intro a r s h1 h2 h3
    rw [h3]
    -- we can show that $r \geq 2$ and $s \geq 4$.
    have hx : r ≥ 2 := by linarith
    have hy : s ≥ 4 := by linarith
    -- Just need to show $s \leq 2r$.
    rw [div_le_div_iff₀ (by norm_num) (by norm_cast; linarith)]
    norm_cast
    simp
    linarith