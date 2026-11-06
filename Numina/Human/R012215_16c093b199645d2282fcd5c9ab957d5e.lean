import Mathlib

/- The domain of the function $f$ is the set of real numbers. For every number $a$, if $a<x<a+100$, then $a \leq f(x) \leq a+100$. Determine the function $f$! -/
theorem algebra_194042 (f : ℝ → ℝ) (hf : ∀ a, ∀ x, a < x ∧ x < a + 100 → a ≤ f x ∧ f x ≤ a + 100) :
    ∀ x, f x = x := by
  -- Use contradiction
  by_contra! neq_id
  -- There is some y where f y ≠ y
  rcases neq_id with ⟨y, hy⟩
  -- Casework on whether f y is less than or greater than
  apply lt_or_gt_of_ne at hy
  rcases hy with f_lt | f_gt
  · -- f y < y
    -- There exists an a such that y ∈ (a, a + 100) but f y < a
    have ex_inbetween : ∃ a, a < y ∧ y < a + 100 ∧ f y < a := by
      -- Do casework on whether y - f y is less than or greater than 100
      have : y - f y < 100 ∨ 100 ≤ y - f y := lt_or_le (y - f y) 100
      rcases this with diff_lt | diff_ge
      · -- Use the midpoint of f y and y when y and f y are close
        use (f y + y) / 2
        exact ⟨by linarith, by linarith, by linarith⟩
      -- Use y - 1 when y and f y are far
      use y - 1
      exact ⟨by linarith, by linarith, by linarith⟩
    rcases ex_inbetween with ⟨a, ha⟩
    specialize hf a y
    -- The interval [a, a + 100] violates hf
    linarith [(hf ⟨ha.1, ha.2.1⟩).1]
  -- y < f y
  -- There exists an a such that y ∈ (a, a + 100) but a + 100 < f y
  have ex_inbetween : ∃ a, a < y ∧ y < a + 100 ∧ a + 100 < f y := by
    -- Do casework on whether or not f y - y is less than or greater than 100
    have : f y - y < 100 ∨ 100 ≤ f y - y := lt_or_le (f y - y) 100
    rcases this with diff_lt | diff_ge
    · -- Make a + 100 the midpoint of y and f y when the difference is small
      use (f y + y) / 2 - 100
      exact ⟨by linarith, by linarith, by linarith⟩
    -- Use y - 1 when y and f y are far
    use y - 1
    exact ⟨by linarith, by linarith, by linarith⟩
  rcases ex_inbetween with ⟨a, ha⟩
  specialize hf a y
  -- The interval [a, a + 100] violates hf
  linarith [(hf ⟨ha.1, ha.2.1⟩).2]