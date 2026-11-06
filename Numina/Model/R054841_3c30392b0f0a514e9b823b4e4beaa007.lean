import Mathlib

theorem algebra_11490 (a : ℕ → ℝ) (ha1 : a 1 = 1 / 2)
    (han : ∀ n > 0, a (n + 1) = 2 * a n / (3 * a n + 2)) :
    a 2017 = 1 / 3026 := by
  have h3 : ∀ (n : ℕ), a (n + 1) = 1 / (2 + (n : ℝ) * (3 / 2)) := by
    intro n
    induction n with
    | zero =>
      -- base case n = 0
      norm_num [ha1]
    | succ n ih =>
      -- induction hypothesis: a (n + 1) = 1 / (2 + (n : ℝ) * (3 / 2))
      -- need to prove: a ((n + 1) + 1) = 1 / (2 + ((n + 1) : ℝ) * (3 / 2))
      have h4 : a (n + 2) = 2 * a (n + 1) / (3 * a (n + 1) + 2) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [h4, ih]
      field_simp
      <;> ring_nf <;> field_simp
      <;> ring_nf <;> field_simp
      <;> tauto
  specialize h3 2016
  norm_num at h3 ⊢
  exact h3