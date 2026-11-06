import Mathlib

theorem algebra_195069 (x : ℝ) (h : ∑ i ∈ Finset.range 2021, (x + 20.21 * i) = 11.1 * 2021 * 2021) :
    x = 2021 := by
  have h1 : ∑ i in Finset.range 2021, (x + 20.21 * i) = 2021 * x + 20.21 * (∑ i in Finset.range 2021, (i : ℝ)) := by
    simp [Finset.sum_add_distrib]
    <;> ring
  have h2 : ∑ i in Finset.range 2021, (i : ℝ) = (2021 * (2021 - 1 : ℝ) / 2) := by 
    have h3 : ∀ n : ℕ, ∑ i in Finset.range n, (i : ℝ) = ((n : ℝ) * (n - 1 : ℝ) / 2) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp at *
        ring_nf
    specialize h3 2021
    norm_num at h3 ⊢
    all_goals linarith
  have h3 : ∑ i ∈ Finset.range 2021, (x + 20.21 * i) = 2021 * x + 20.21 * (2021 * (2021 - 1 : ℝ) / 2) := by
    rw [h1, h2]
  rw [h3] at h
  ring_nf at h ⊢
  linarith