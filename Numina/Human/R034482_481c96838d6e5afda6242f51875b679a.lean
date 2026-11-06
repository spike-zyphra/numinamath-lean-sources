import Mathlib

open Real

/- 6. Let $0 < x_{i}<\pi(i=1,2, \cdots, n) $, prove: $\prod_{i=1}^{n} \sin x_{i} \leqslant\left[\sin \left(\frac{1}{n} \sum_{i=1}^{n} x_{i}\right)\right]^{n}$. -/
theorem inequalities_217011 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i < Real.pi) :
    ∏ i, sin (x i) ≤ (sin (1 / n * ∑ i, x i))^n := by
  -- We have 0 < sin (x i) because x i ∈ (0, π) for all i.
  have hsin i : 0 < sin (x i) := sin_pos_of_pos_of_lt_pi (hx i).1 (hx i).2
  have hineq : 0 < 1 / (n : ℝ) := by field_simp; exact hn
  -- The set of indices i is non-empty because 0 < n.
  have haux : (Finset.univ : Finset (Fin n)).Nonempty := by
      rw [Finset.Nonempty.eq_1]
      use ⟨0, hn⟩
      simp only [Finset.mem_univ]
  -- Apply log (a strictly increasing function on (0, ∞)) to the both sides of the inequality.
  rw [← strictMonoOn_log.le_iff_le]
  rotate_left
  -- We need to show that ∏ i, sin (x i) > 0. This follows from sin (x i) > 0 for all i.
  · simp only [Set.mem_Ioi]
    apply Finset.prod_pos
    simp only [Finset.mem_univ, forall_const]
    assumption
  -- We also need to show that 0 < sin (1 / n * ∑ i, x i) ^ n.
  · simp only [Set.mem_Ioi]
    apply pow_pos
    -- It is enought to show that 0 < sin (1 / n * ∑ i, x i).
    apply sin_pos_of_pos_of_lt_pi
    -- Show that 0 < 1 / n * ∑ i, x i.
    · field_simp
      apply Finset.sum_pos _ haux
      simp only [Finset.mem_univ, forall_const]
      intro i
      exact (hx i).1
    -- Show that 1 / n * ∑ i, x i < π.
    · calc
        1 / n * ∑ i, x i < 1 / n * ∑ i : Fin n, π := by
            gcongr with i
            · exact haux
            · exact (hx i).2
        _ = π := by field_simp
  -- Rewrite the inequality as follows:
  -- ∑ i, log (sin (x i)) ≤ n * log (sin (1 / n * ∑ i, x i)).
  rw [log_prod _ _ (fun i _ => ne_of_gt (hsin i)), log_pow]
  -- The goal is equivalent to
  -- ∑ i, 1 / n * log (sin (x i)) ≤ log (sin (∑ i, 1 / n * x i)).
  apply le_of_mul_le_mul_left _ hineq
  simp_rw [Finset.mul_sum, ← mul_assoc, show (1 / n : ℝ) * n = 1 by field_simp, one_mul]
  -- Prove that the function log ∘ sin is concave on (0, π).
  have hco : ConcaveOn ℝ (Set.Ioo 0 π) (log ∘ sin) := by
    -- Show that sin '' (0, π) = (0, 1].
    have h : sin '' Set.Ioo 0 π = Set.Ioc 0 1 := by
      -- Prove that sin '' (0, π) ⊆ (0, 1] and (0, 1] ⊆ sin '' (0, π).
      rw [Set.Subset.antisymm_iff]
      constructor
      · intro y
        -- Show that y = sin(x) for x ∈ (0, π) implies that sin(x) ∈ (0, 1].
        simp only [Set.mem_image, Set.mem_Ioo, forall_exists_index, and_imp]
        intro x hx1 hx2 eq
        subst y
        -- The result follows from sin(x) ≤ 1 for all x and 0 < sin(x) for x ∈ (0, π).
        exact ⟨sin_pos_of_pos_of_lt_pi hx1 hx2, sin_le_one x⟩
      · nth_rw 1 [← sin_zero, ← sin_pi_div_two]
        -- We have (0, 1] = (sin 0, sin (π / 2)] ⊆ sin '' (0, π / 2] (by the intermediate value theorem).
        -- We also have sin '' (0, π / 2] ⊆ sin '' (0, π) so (0, 1] ⊆ sin '' (0, π).
        trans sin '' Set.Ioc 0 (π / 2)
        · exact intermediate_value_Ioc (by linarith [pi_pos]) (by fun_prop)
        · apply Set.image_subset
          apply Set.Ioc_subset_Ioo_right
          linarith [pi_pos]
    -- Now we can show that log ∘ sin is concave on (0, π).
    apply ConcaveOn.comp
    -- We need to show that log is concave on sin '' (0, π) = (0, 1].
    -- This follows from the fact that log is strictly concave on (0, ∞).
    · rw [h]
      apply StrictConcaveOn.concaveOn
      exact StrictConcaveOn.subset strictConcaveOn_log_Ioi Set.Ioc_subset_Ioi_self (convex_Ioc 0 1)
    -- We need to show that sin is concave on (0, π).
    -- This follows from the fact that sin is strictly concave on [0, π].
    · apply StrictConcaveOn.concaveOn
      apply strictConcaveOn_sin_Icc.subset Set.Ioo_subset_Icc_self (convex_Ioo 0 π)
    -- We need to show that log is monotone on (0, 1].
    -- This follows from the fact that log is strictly monotone on (0, ∞).
    · rw [h]
      apply StrictMonoOn.monotoneOn
      apply Real.strictMonoOn_log.mono
      exact Set.Ioc_subset_Ioi_self
  -- We proved that log ∘ sin is concave on (0, π).
  -- Jensen's inequality applied to log ∘ sin and to 1 / n * x i implies
  -- ∑ i, 1 / n * log (sin (x i)) ≤ log (sin (∑ i, 1 / n * x i)).
  -- It is left to prove that 0 ≤ 1 / n, ∑ i, 1 / n = 1, and x(i) ∈ (0, π).
  -- All these results are easy to prove.
  apply hco.le_map_sum
  · intro _ _
    exact le_of_lt hineq
  · field_simp
  · simp only [Finset.mem_univ, Set.mem_Ioo, forall_const]
    exact hx