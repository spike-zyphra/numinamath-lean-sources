import Mathlib

/-
1. Let $a, b$ be rational numbers, and $|a|>0$, the equation $||x-a|-b|=5$ has three distinct roots. Then $b=(\quad)$.
(A) 1
(B) 3
(C) 5
(D) 6
 -/
theorem algebra_325526 (a b : ℚ) (ha : |a| > 0) :
    {x | |(|x - a| - b)| = 5}.ncard = 3 ↔ b = 5 := by
  -- \-,1. C. From the given, we have $$ |x \sim a|=b+5 \text { or } b-5 \text {. } $$
  let t₁ := ({b + 5, b - 5} : Finset ℚ)
  let t₂ := t₁.filter (. ≥ 0)
  -- Proving disjoint would actually be simpler with `{x | |(|x - a| - b)| = 5} = {x | |x - a| = b + 5} ∪ {x | |x - a| = b - 5}`.
  let t := t₂.disjiUnion (fun b' => {a + b', a - b'}) (by
    simp [Set.PairwiseDisjoint, Set.Pairwise, t₂]
    --simp [Finsetet.pairwiseDisjoint_iff]
    intro b'₁ _ b'₁_nonneg b'₂ _ b'₂_nonneg ne
    have : ¬b'₂ = b'₁ := by
      exact fun eq ↦ ne (id (Eq.symm eq))
    constructor
    . constructor
      . exact this
      . intro eq
        have : b'₁ = b'₂ := by linarith
        contradiction
    . constructor
      . intro eq
        have : b'₁ = b'₂ := by linarith
        contradiction
      . exact this
  )
  have : {x | |(|x - a| - b)| = 5} = t := by
    ext x
    simp [t, t₂, t₁]
    constructor
    . intro eq
      use |x - a|
      have := (abs_eq (by simp)).mp eq
      constructor
      . constructor
        . cases this
          . left
            linarith
          . right
            linarith
        . simp
      . have := (abs_eq (by simp)).mp (rfl : |x - a| = |x - a|)
        cases this
        . left
          linarith
        . right
          linarith
    . rintro ⟨b', ⟨b'_eqs, b'_nonneg⟩, x_eqs⟩
      have : |x - a| = b' := by
        have : x - a = b' ∨ x - a = -b' := by
          cases x_eqs
          . left
            linarith
          . right
            linarith
        exact (abs_eq b'_nonneg).mpr this
      rw [this]
      show |b' - b| = 5
      have : b' - b = 5 ∨ b' - b = -5 := by
        cases b'_eqs
        . left
          linarith
        . right
          linarith
      exact (abs_eq (by simp)).mpr this
  simp [this]
  unfold t
  rw [Finset.card_disjiUnion]
  -- And each equation has two, one, or zero solutions. Since the original equation has three distinct roots, one equation has two solutions, and the other has one solution. Therefore, one of the non-negative numbers $b+5, b-5$ must be 0. Thus, $b=5$. At this point, $x=a+10, a-10, a$ are all solutions to the original equation.
  by_cases w_b_eq : b = 5
  . simp [w_b_eq]
    have : t₂ = {0, 10} := by
      simp [t₂, t₁, w_b_eq]
      native_decide
    rw [this]
    simp
    suffices ({a + 10, a - 10} : Finset ℚ).card = 2 by
      linarith
    refine Finset.card_pair ?_
    linarith
  simp [w_b_eq]
  by_cases w_b_gt_5 : b > 5
  . suffices ∑ b' ∈ t₂, ({a + b', a - b'} : Finset ℚ).card = 4 by
      linarith
    have : t₂ = {b + 5, b - 5} := by
      simp [t₂, t₁]
      ext b'
      simp
      intro b'_eqs
      cases b'_eqs <;>
      . linarith
    rw [this]
    suffices ∀ b' ∈ ({b + 5, b - 5} : Finset ℚ), ({a + b', a - b'} : Finset ℚ).card = 2 by
      simp [Finset.sum_congr rfl this]
      suffices ({b + 5, b - 5} : Finset ℚ).card = 2 by
        linarith
      refine Finset.card_pair ?_
      linarith
    intro b' b'_in
    apply Finset.card_pair
    have : b' > 0 := by
      simp at b'_in
      cases b'_in <;>
      . linarith
    linarith
  . have : b < 5 := by
      simp at w_b_gt_5
      exact lt_of_le_of_ne w_b_gt_5 w_b_eq
    suffices ∑ b' ∈ t₂, ({a + b', a - b'} : Finset ℚ).card ≤ 2 by
      linarith
    have : t₂ ⊆ {b + 5} := by
      dsimp [t₂, t₁]
      intro b'
      simp
      rintro b'_eqs b'_nonneg
      cases b'_eqs <;>
      . linarith
    have : t₂.card ≤ ({b + 5} : Finset ℚ).card := by
      exact Finset.card_le_card this
    norm_num at this
    suffices ∀ b' ∈ ({b + 5, b - 5} : Finset ℚ), ({a + b', a - b'} : Finset ℚ).card ≤ 2 by
      by_cases h : t₂.card = 1
      . have : ∃ b', t₂ = {b'} := by
          exact Finset.card_eq_one.mp h
        rcases this with ⟨b', t₂_eq⟩
        rw [t₂_eq]
        simp
        exact Finset.card_le_two
      . have : t₂.card = 0 := by
          omega
        have : t₂ = ∅ := by
          exact Finset.card_eq_zero.mp this
        rw [this]
        simp
    intro b' b'_in
    exact Finset.card_le_two
