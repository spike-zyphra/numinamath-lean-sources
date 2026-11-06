import Mathlib

theorem algebra_328471 (a : ℝ) (A B : Set ℝ) (hA : A = {x | a * x + 2 = 0}) (hB : B = {-1, 2})
    (hAB : A ⊆ B) :
    a = -1 ∨ a = 0 ∨ a = 2 := by
  by_cases ha : a = 0
  · -- If a = 0, then A is empty.
    right
    left
    exact ha
  · -- If a ≠ 0, then solving ax + 2 = 0 gives x = -2/a
    have ha' : a ≠ 0 := by
      intro h
      apply ha
      linarith
    have hA_nonempty : A = { -2 / a } := by
      ext x
      simp [hA]
      constructor
      · -- Suppose x ∈ A, so a * x + 2 = 0, then x = -2/a.
        intro h
        field_simp at h ⊢
        nlinarith [sq_pos_of_ne_zero ha']
      · -- Suppose x = -2/a, need to prove a * x + 2 = 0.
        intro h_eq
        rw [h_eq]
        field_simp at *
        <;> ring_nf <;> field_simp [ha']
        <;> nlinarith [sq_pos_of_ne_zero ha']
        all_goals linarith
    -- Since A = { -2/a }, and A ⊆ B, so -2/a ∈ B
    have h1 : -2 / a ∈ B := by
      have h2 : -2 / a ∈ A := by
        simp [hA_nonempty]
      exact hAB h2
    rw [hB] at h1
    simp at h1
    cases h1 with
    | inl h_eq_neg1 =>
      -- Case where -2/a = -1
      have : a = 2 := by
        field_simp at h_eq_neg1
        linarith
      right
      right
      exact this
    | inr h_eq_2 =>
      -- Case where -2/a = 2
      have : a = -1 := by
        field_simp at h_eq_2
        linarith
      left
      exact this