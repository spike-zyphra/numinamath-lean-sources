import Mathlib

theorem algebra_135085 : ∑ i ∈ Finset.range 11, Real.pi ^ i = (Real.pi ^ 11 - 1) / (Real.pi - 1) := by
  have h1 : Real.pi - 1 ≠ 0 := by
    have h2 : Real.pi > 3 := Real.pi_gt_three
    linarith

  have h : ∀ n : ℕ, ∑ i in Finset.range n, Real.pi ^ i = (Real.pi ^ n - 1) / (Real.pi - 1) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> field_simp [h1]
      <;> ring_nf
    | succ n ih =>
      have h' : ∑ i in Finset.range (n + 1), Real.pi ^ i = (∑ i in Finset.range n, Real.pi ^ i) + Real.pi ^ n := by
        rw [Finset.sum_range_succ]
      rw [h']
      rw [ih]
      field_simp [(show Real.pi - 1 ≠ 0 from h1)]
      <;> ring_nf

  specialize h 11
  simpa using h