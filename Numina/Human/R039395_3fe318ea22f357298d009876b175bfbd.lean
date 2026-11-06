import Mathlib

open Real Finset

/- 8. Evaluate $\sum_{n=0}^{\infty} \cot ^{-1}\left(n^{2}+n+1\right)$. -/
theorem calculus_185111 : ∑' n : ℕ, arctan (1 / (n^2 + n + 1)) = π / 2 := by
  -- Rewrite the theorem statement in terms of HasSum
  suffices HasSum (fun n : ℕ => arctan (1 / (n^2 + n + 1))) (π / 2) from this.tsum_eq
  -- Rewrite the theorem statement as
  -- lim (∑ i ∈ range n, arctan (1 / (i ^ 2 + i + 1)) = π / 2.
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  swap
  -- Show that 0 ≤ arctan (1 / (n^2 + n + 1)) for all n.
  · intro n
    rw [← arctan_zero]
    apply arctan_strictMono.monotone
    positivity
  -- Prove that ∑ i ∈ range n, arctan (1 / (i^2 + i + 1)) = arctan n.
  have eq n : ∑ i ∈ range n, arctan (1 / (i ^ 2 + i + 1)) = arctan n := calc
    -- We have arctan(i + 1) - arctan i = arctan ((i + 1 - i) / (1 + (i + 1) * i))
    --      = arctan (1 / (i^2 + i + 1)).
    _ = ∑ i ∈ range n, (arctan ((i + 1 : ℕ)) + arctan (-i)) := by
      apply sum_congr rfl
      intro i hi
      rw [arctan_add (by nlinarith)]
      congr 1
      field_simp
      ring
    -- The sum ∑ i ∈ range n, (arctan(i + 1) - arctan i) is telescoping
    -- so it equals to arctan n - arctan 0 = arctan n.
    _ = arctan n := by
      simp_rw [arctan_neg, ←sub_eq_add_neg]
      rw [sum_range_sub (f := fun i => arctan i)]
      simp
  simp_rw [eq]
  -- Show that lim (arctan(n)) = π / 2 as n tends to infinity.
  apply Filter.Tendsto.comp (g := arctan) (y := .atTop)
  -- lim (arctan(x)) = π / 2 as x tends to infinity.
  · apply Filter.Tendsto.mono_right tendsto_arctan_atTop
    exact nhdsWithin_le_nhds
  -- lim n = infinity as n tends to infinity.
  · exact tendsto_natCast_atTop_atTop