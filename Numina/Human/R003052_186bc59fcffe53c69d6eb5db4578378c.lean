import Mathlib

-- Show that if there is exactly one solution to |x + 1| = ax + 2, then a ≤ -1 or 1 ≤ a.
lemma forward_direction (a : ℝ) : ({(x, y) : ℝ × ℝ | y = a * x + 2 ∧ y = |x + 1|}).encard = 1 → a ≤ -1 ∨ 1 ≤ a := by
  -- Equivalently, show that for -1 < a < 1, there are two solutions to |x + 1| = ax + 2.
  contrapose
  intro ha
  simp at ha ⊢
  suffices {(x, y) : ℝ × ℝ | y = a * x + 2 ∧ y = |x + 1|}.encard = 2 by
    simp [this]
  rw [Set.encard_eq_two]
  -- The two solutions are (-1 / (a - 1), (a - 2)/(a - 1)) and (-3 / (a + 1), (-a + 2)/(a + 1)).
  use (-1 / (a - 1), (a - 2) / (a - 1)), (-3 / (a + 1), (-a + 2) / (a + 1))
  refine ⟨?_, ?_⟩
  . -- First show that these two solutions are distinct.
    field_simp [show a - 1 ≠ 0 by linarith, show a + 1 ≠ 0 by linarith]
    intro _
    linarith
  . -- Now show that these are exactly the solutions to the set.
    ext ⟨x, y⟩
    simp
    constructor
    . -- Show that y = ax + 2 = |x + 1| implies the two solutions.
      rintro ⟨h₀, h₁⟩
      have h₂ := abs_choice (x + 1)
      rw [<-h₁] at h₂
      rcases h₂ with (h₂ | h₂)
      . -- y = x + 1 corresponds to the left case.
        left
        field_simp [show a - 1 ≠ 0 by linarith]
        exact ⟨by linarith, by nlinarith⟩
      . -- y = -x - 1 corresponds to the right case.
        right
        field_simp [show a + 1 ≠ 0 by linarith]
        exact ⟨by linarith, by nlinarith⟩
    . -- Show that the two solutions are indeed valid.
      rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      . simp [hx, hy]
        refine ⟨?_, ?_⟩
        . field_simp [show a - 1 ≠ 0 by linarith]
          ring
        . rw [neg_div, neg_add_eq_sub, one_sub_div, abs_of_nonneg]
          . ring
          . apply div_nonneg_of_nonpos
            <;> linarith
          . linarith
      . simp [hx, hy]
        refine ⟨?_, ?_⟩
        . field_simp [show a + 1 ≠ 0 by linarith]
          ring
        . rw [neg_div, neg_add_eq_sub _ 1, one_sub_div, abs_of_nonpos]
          . ring
          . apply div_nonpos_of_nonpos_of_nonneg
            <;> linarith
          . linarith

-- Show that for a ≤ -1 or a ≥ 1, there is exactly one solution to |x + 1| = ax + 2.
lemma backward_direction (a : ℝ) : a ≤ -1 ∨ 1 ≤ a → ({(x, y) : ℝ × ℝ | y = a * x + 2 ∧ y = |x + 1|}).encard = 1 := by
  rintro (ha | ha)
  <;> rw [Set.encard_eq_one]
  . -- The solution is (-1 / (a - 1), (a - 2) / (a - 1)).
    use (-1 / (a - 1), (a - 2) / (a - 1))
    ext ⟨x, y⟩
    simp
    constructor
    . -- Show that y = ax + 2 = |x + 1| implies the solution.
      rintro ⟨h₀, h₁⟩
      have h₂ := abs_cases (x + 1)
      rw [<-h₁] at h₂
      rcases h₂ with (h₂ | h₂)
      . -- y = x + 1 gives the solution.
        field_simp [show a - 1 ≠ 0 by linarith]
        exact ⟨by linarith, by nlinarith⟩
      . -- y = -x - 1 gives a contradiction.
        rw [h₂.1] at h₀
        replace h₀ : (a + 1) * x = -3 := by
          linarith
        have hx : x ≥ 0 := by
          nlinarith
        linarith
    . -- Show that the solution is indeed valid.
      rintro ⟨hx, hy⟩
      simp [hx, hy]
      refine ⟨?_, ?_⟩
      . field_simp [show a - 1 ≠ 0 by linarith]
        ring
      . rw [neg_div, neg_add_eq_sub, one_sub_div, abs_of_nonneg]
        . ring
        . apply div_nonneg_of_nonpos
          <;> linarith
        . linarith
  . -- Separate the cases for a ≥ 2 and 1 ≤ a < 2.
    by_cases ha' : a ≥ 2
    . -- The solution is (-1 / (a - 1), (a - 2) / (a - 1)).
      use (-1 / (a - 1), (a - 2) / (a - 1))
      ext ⟨x, y⟩
      simp
      constructor
      . -- Show that y = ax + 2 = |x + 1| implies the solution.
        rintro ⟨h₀, h₁⟩
        have h₂ := abs_cases (x + 1)
        rw [<-h₁] at h₂
        rcases h₂ with (h₂ | h₂)
        . -- y = x + 1 gives the solution.
          field_simp [show a - 1 ≠ 0 by linarith]
          exact ⟨by linarith, by nlinarith⟩
        . -- y = -x - 1 gives a contradiction.
          rw [h₂.1] at h₀
          replace h₀ : (a + 1) * x = -3 := by
            linarith
          have hx : x ≥ -1 := by
            nlinarith
          linarith
      . -- Show that the solution is indeed valid.
        rintro ⟨hx, hy⟩
        simp [hx, hy]
        refine ⟨?_, ?_⟩
        . field_simp [show a - 1 ≠ 0 by linarith]
          ring
        . rw [neg_div, neg_add_eq_sub, one_sub_div, abs_of_nonneg]
          . ring
          . apply div_nonneg
            <;> linarith
          . linarith
    . -- The solution is (-3 / (a + 1), (-a + 2) / (a + 1)).
      use (-3 / (a + 1), (-a + 2) / (a + 1))
      ext ⟨x, y⟩
      simp
      constructor
      . -- Show that y = ax + 2 = |x + 1| implies the solution.
        rintro ⟨h₀, h₁⟩
        have h₂ := abs_cases (-(x + 1))
        simp only [abs_neg] at h₂
        rw [<-h₁] at h₂
        rcases h₂ with (h₂ | h₂)
        . -- y = -x - 1 gives the solution.
          field_simp [show a + 1 ≠ 0 by linarith]
          exact ⟨by linarith, by nlinarith⟩
        . -- y = x + 1 gives a contradiction.
          rw [h₂.1] at h₀
          replace h₀ : (a - 1) * x = -1 := by
            linarith
          have hx : x ≤ -1 := by
            nlinarith
          linarith
      . -- Show that the solution is indeed valid.
        rintro ⟨hx, hy⟩
        simp [hx, hy]
        refine ⟨?_, ?_⟩
        . field_simp [show a + 1 ≠ 0 by linarith]
          ring
        . rw [neg_div, neg_add_eq_sub _ 1, one_sub_div, abs_of_nonpos]
          . ring
          . apply div_nonpos_of_nonpos_of_nonneg
            <;> linarith
          . linarith

/- 1. Given the sets $A=\{(x, y) \mid y=a x+2\}, B=$ $\{(x, y) \mid y=| x+1 |\}$, and $A \cap B$ is a singleton set, then the range of the real number $a$ is $\qquad$ .-/
theorem algebra_148748 :
    {a : ℝ | ({(x, y) : ℝ × ℝ | y = a * x + 2} ∩ {(x, y) : ℝ × ℝ | y = |x + 1|}).encard = 1} = Set.Iic (-1) ∪ Set.Ici 1 := by
  ext a
  simp [Set.inter_def]
  -- Break the goal into two parts and apply the lemmas.
  apply Iff.intro
  . apply forward_direction
  . apply backward_direction
