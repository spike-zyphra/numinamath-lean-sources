import Mathlib

theorem algebra_310927 (a : ℝ) (h₁ : {x : ℝ | x^2 - 6 * x + (a - 2) * abs (x - 3) + 9 - 2 * a = 0}.encard = 2) : a = -2 ∨ a > 0 := by
  -- We can prove this by contradiction.
  by_contra!
  obtain ⟨h₄, h₅⟩ := this

  -- First, we split the set into two parts depending on the sign of `x - 3`.
  have h₂ : {x : ℝ | x^2 - 6 * x + (a - 2) * abs (x - 3) + 9 - 2 * a = 0} = {x : ℝ | x^2 - 6 * x + (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 ≥ 0} ∪ {x : ℝ | x^2 - 6 * x - (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 < 0} := by
    ext x; simp
    constructor
    · intro hx₁
      obtain (hx₂ | hx₂) := abs_choice (x - 3) <;> rw [hx₂] at hx₁
      · apply Or.inl
        exact ⟨by linarith, by linarith [abs_eq_self.mp hx₂]⟩
      · by_cases hx₃ : x = 3
        · rw [hx₃] at hx₁ ⊢
          norm_num at hx₁ ⊢
          exact hx₁
        apply Or.inr
        exact ⟨by linarith, lt_of_le_of_ne (by linarith [abs_eq_neg_self.mp hx₂]) hx₃⟩
    · rintro (⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩)
      · rw [abs_eq_self.mpr (by linarith)]
        linarith
      · rw [abs_eq_neg_self.mpr (by linarith)]
        linarith
  -- Then, we prove that the two sets are disjoint.
  have h₃ : Disjoint {x : ℝ | x ^ 2 - 6 * x + (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 ≥ 0} {x : ℝ | x ^ 2 - 6 * x - (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 < 0} := by
    rw [Set.disjoint_left]
    simp
    intro _ _ _ _
    linarith
  rw [h₂, Set.encard_union_eq h₃] at h₁

  -- Because a ≤ 0 ∧ a ≠ -2, so, {x : ℝ | x ^ 2 - 6 * x + (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 ≥ 0} = {5, 3 - a}
  have h₆ : {x : ℝ | x ^ 2 - 6 * x + (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 ≥ 0}.encard = 2 := by
    suffices {x : ℝ | x ^ 2 - 6 * x + (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 ≥ 0} = {5, 3 - a} by
      rw [this, Set.encard_eq_two]
      use 5
      use 3 - a
      simp
      intro ha
      exact h₄ (by linarith)
    ext x; simp
    constructor
    · rintro ⟨hx₁, hx₂⟩
      have hx₃ : (x - 5) * (x - (3 - a)) = 0 := by linarith
      simp at hx₃
      obtain (hx₃ | hx₃) := hx₃
      · apply Or.inl
        linarith
      · apply Or.inr
        linarith
    · rintro (hx₁ | hx₁) <;>
        rw [hx₁] <;>
        ring_nf <;>
        simp <;>
        linarith

  -- {x | x ^ 2 - 6 * x - (a - 2) * (x - 3) + 9 - 2 * a = 0} is finite, and this set is a subset of it, so this set is finite too.
  have h₇ : {x : ℝ | x ^ 2 - 6 * x - (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 < 0}.Finite := by
    have : {x | x ^ 2 - 6 * x - (a - 2) * (x - 3) + 9 - 2 * a = 0}.Finite := by
      suffices {x | x ^ 2 - 6 * x - (a - 2) * (x - 3) + 9 - 2 * a = 0} = {1, 3 + a} by
        rw [this]
        norm_num
      ext x; simp
      constructor
      · intro hx₁
        have hx₂ : (x - 1) * (x - (3 + a)) = 0 := by linarith
        simp at hx₂
        obtain (hx₂ | hx₂) := hx₂
        · apply Or.inl
          linarith
        · apply Or.inr
          linarith
      · rintro (hx₁ | hx₁) <;>
          rw [hx₁] <;>
          ring_nf
    apply Set.Finite.subset this
    simp
    intro _ _ _
    assumption

  -- {x : ℝ | x ^ 2 - 6 * x - (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 < 0}.Finite means that its encard equals ncard.
  rw [h₆, ←Set.Finite.cast_ncard_eq h₇] at h₁
  norm_cast at h₁
  -- But, we know that 1 is in this set, so its ncard is at least 1.
  have h₈ : 0 < {x | x ^ 2 - 6 * x - (a - 2) * (x - 3) + 9 - 2 * a = 0 ∧ x - 3 < 0}.ncard := by
    rw [Set.ncard_pos h₇]
    use 1
    simp
    ring_nf
  -- There is a contradiction between h₁ and h₈. h₁ states that the ncard is zero, and h₈ states that the ncard is at least one.
  linarith
