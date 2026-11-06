import Mathlib

theorem algebra_611147 (f : ℝ → ℝ) (hf : f = fun x ↦ if x < 1 then 0 else 2 * x - 2) :
    {x | f (f (f (f x))) = x}.encard = 2 := by
  -- We show that {x | f (f (f (f x))) = x} = {0, 2}
  suffices H : {x | f (f (f (f x))) = x} = {0, 2} by
    simp [H, Set.encard_pair]
  ext x
  simp
  constructor
  -- We first verify that 0 and 2 are in the set
  swap
  {
    rintro (rfl | rfl)
    . simp [hf]
    . norm_num [hf]
  }
  -- We now show that no other number is in the set
  intro H
  by_contra! k
  -- If x ≠ 0 and x ≠ 2, then x < 0 or 0 < x < 2 or x > 2
  replace k : x < 0 ∨ 0 < x ∧ x < 2 ∨ x > 2 := by
    rcases lt_or_gt_of_ne k.1 with h | h
    . exact Or.inl h
    . rcases lt_or_gt_of_ne k.2 with h' | h'
      . exact Or.inr (Or.inl ⟨h, h'⟩)
      . exact Or.inr (Or.inr h')
  -- We show that any of these cases leads to a contradiction
  rcases k with k | k | k
  . -- 1. x < 0
    -- f always takes non-negative values
    have h x : f x ≥ 0 := by
      simp [hf]
      -- Split into cases
      split_ifs with hx
      . simp
      . linarith only [hx]
    -- So f (f (f (f x))) ≥ 0
    specialize h (f (f (f x)))
    -- Contradiction
    linarith only [H, k, h]
  . -- 2. 0 < x ∧ x < 2
    -- We have 0 ≤ f x < x < 2 when 0 < x < 2
    have h {x} (hx : 0 < x ∧ x < 2) : f x < x ∧ 0 ≤ f x ∧ f x < 2 := by
      simp [hf]
      -- Split into cases
      split_ifs with hx'
      . simp [hx.1]
      . refine ⟨?_, ?_, ?_⟩
        all_goals linarith only [hx, hx']
    -- A variant of the lemma above
    -- If 0 ≤ x < 2, then 0 ≤ f x ≤ x < 2
    have h' {x} (hx : 0 ≤ x ∧ x < 2) : f x ≤ x ∧ 0 ≤ f x ∧ f x < 2 := by
      simp [hf]
      -- Split into cases
      split_ifs with hx'
      . simp [hx.1]
      . refine ⟨?_, ?_, ?_⟩
        all_goals linarith only [hx, hx']
    -- So we have 0 ≤ f (f (f (f x))) ≤ f (f (f x)) ≤ f (f x) ≤ f x < x < 2
    have ⟨s₁, k₁⟩ := h k
    have ⟨s₂, k₂⟩ := h' k₁
    have ⟨s₃, k₃⟩ := h' k₂
    have ⟨s₄, k₄⟩ := h' k₃
    -- Contradiction
    linarith only [s₁, s₂, s₃, s₄, H]
  . -- 3. x > 2
    -- We have f x > x > 2 when x > 2
    have h {x} (hx : x > 2) : f x > x ∧ f x > 2 := by
      simp [hf]
      -- Split into cases
      split_ifs with hx'
      . linarith only [hx, hx']
      . refine ⟨?_, ?_⟩
        all_goals linarith only [hx, hx']
    -- So we have f (f (f (f x))) > f (f (f x)) > f (f x) > f x > x > 2
    have ⟨s₁, k₁⟩ := h k
    have ⟨s₂, k₂⟩ := h k₁
    have ⟨s₃, k₃⟩ := h k₂
    have ⟨s₄, k₄⟩ := h k₃
    -- Contradiction
    linarith only [s₁, s₂, s₃, s₄, H]
