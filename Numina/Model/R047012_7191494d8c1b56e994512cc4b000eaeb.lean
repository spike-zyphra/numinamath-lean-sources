import Mathlib

theorem number_theory_26899 (r : ℝ) (hr : r = 2) :
    Set.Infinite {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 = r ^ 2 ∧ ∃ q1 q2 : ℚ, x = q1 ∧ y = q2} := by
  rw [hr]
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ((4 * (n : ℝ) + 2) / (2 * (n : ℝ) ^ 2 + 2 * (n : ℝ) + 1), (4 * (n : ℝ) * ((n : ℝ) + 1)) / (2 * (n : ℝ) ^ 2 + 2 * (n : ℝ) + 1)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    rcases h with ⟨hx, hy⟩
    have eq1 := hx
    field_simp at eq1
    ring_nf at eq1
    have eq2 := hy
    field_simp at eq2
    ring_nf at eq2
    have h1 : (n : ℝ) = (m : ℝ) := by
      nlinarith [sq_nonneg ((n : ℝ) - (m : ℝ)), sq_nonneg ((n : ℝ) + (m : ℝ) + 1 / 2)]
    exact_mod_cast h1
  · -- Show that all points from f are in the set
    intro n
    simp [Prod.ext_iff]
    constructor
    · -- Verify the point satisfies the equation x^2 + y^2 = 4
      field_simp
      ring_nf
    · -- Verify that the coordinates are rational
      constructor
      · -- First coordinate is rational
        use (4 * ((n : ℚ)) + 2) / (2 * ((n : ℚ)) ^ 2 + 2 * (n : ℚ) + 1)
        all_goals norm_num
        <;> ring_nf <;> norm_num
      · -- Second coordinate is rational
        use (4 * ((n : ℚ)) * ((n : ℚ) + 1)) / (2 * ((n : ℚ)) ^ 2 + 2 * (n : ℚ) + 1)
        all_goals norm_num
        <;> ring_nf <;> norm_num