import Mathlib

/- As is known, a quadratic equation has no more than two roots. Can the equation $\$[x \wedge 2]+p x+q=0 \$\$ for \$p \ne 0 have more than 100 roots? (\$ \$x^2]\$ denotes the greatest integer not exceeding \$x^2\$.) -/
theorem algebra_181373 : ∃ (p q : ℝ), p ≠ 0 ∧ 100 ≤ {x : ℝ | ⌊x ^ 2⌋ + p * x + q = 0}.encard := by
  -- we'll show p = -100, q = 2500 implies equation has more than 100 roots
  use -100, 2500
  norm_num
  -- we'll show 50 + k/100 for k = 0...99 are roots, so first we show they are subset of roots
  have h₁ : {(50 + k / 100 : ℝ)| (k : ℕ)  (_ : k ≤ 99)} ⊆ {x | ↑⌊x ^ 2⌋ + -(100 * x) + 2500 = 0} := by
    simp
    rintro k hk
    ring_nf
    -- we can take out 2500 + k from floor
    rw [show (2500 + k : ℝ) = ↑(2500 + k :ℕ) by norm_cast, Int.floor_nat_add]
    push_cast
    ring_nf
    norm_cast
    -- now we show ⌊k^2 / 10000⌋ is 0
    refine Int.floor_eq_iff.mpr ?_
    and_intros
    . norm_cast
      positivity
    . norm_num
      nth_rw 2 [show (1 : ℝ) = 10000 * (1/10000) by norm_num]
      gcongr
      norm_cast
      rw [show 10000 = (100)^2 by norm_num]
      gcongr
      omega
  -- now the set's cardinaltiy ≤ roots cardinality, we'll show set's cardinality is 100
  replace h₁ := Set.encard_le_card h₁
  convert h₁
  -- we can show the set as f({0, 1, ..., 99})
  let f (x : ℕ) := (50 + x / 100 : ℝ)
  have h₂ : f '' (Set.Icc 0 99) = {(50 + k / 100 : ℝ)| (k : ℕ)  (_ : k ≤ 99)} := by
    simp [f, Set.image]
  rw [← h₂]
  -- f is injective
  replace h₂ : Function.Injective f := by
    rintro a b hab
    simp [f] at hab
    replace hab := congrArg (· * 100) hab
    ring_nf at hab
    norm_cast at hab
  -- so 100 = {0, 1, ...., 99}
  rw [Function.Injective.encard_image h₂, show Set.Icc 0 99 = (Finset.Icc 0 99) by simp, Set.encard_coe_eq_coe_finsetCard]
  simp