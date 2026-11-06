import Mathlib

theorem Algebra_611432:
  tsum (fun n0 : ℕ => -- Sum starts from n0=0, corresponds to n=2 for the original series index n
          -- Let n be the original series index, n = n0 + 2
          let n : ℕ := n0 + 2
          -- The term of the series
          ( (n:ℝ)^4 + 3 * (n:ℝ)^2 + 10 * (n:ℝ) + 10 ) /
          ( (2 : ℝ)^n * ( (n:ℝ)^4 + 4 ) )
       ) = (11 : ℝ) / 10 := by

  -- Define the helper function for telescoping series
  let f (k : ℕ) : ℝ := (2 : ℝ) / ((2 : ℝ)^k * ((k : ℝ)^2 + 1))

  -- Define the three terms in our decomposed sum
  let term1 (n0 : ℕ) : ℝ := 1 / (2 : ℝ)^(n0 + 2)
  let term2 (n0 : ℕ) : ℝ := f (n0 + 1)
  let term3 (n0 : ℕ) : ℝ := f (n0 + 3)

  -- 1. Partial fraction decomposition of the summand
  have term_rewrite (n0 : ℕ) :
    let n : ℕ := n0 + 2
    ((n : ℝ)^4 + 3 * (n : ℝ)^2 + 10 * (n : ℝ) + 10) / ((2 : ℝ)^n * ((n : ℝ)^4 + 4)) =
    term1 n0 + term2 n0 - term3 n0 := by
    unfold term1 term2 term3 f
    field_simp
    ring_nf


  -- 2. Rewrite the original sum using our term decomposition
  have h1 : tsum (fun n0 =>
                let n : ℕ := n0 + 2
                ((n : ℝ)^4 + 3 * (n : ℝ)^2 + 10 * (n : ℝ) + 10) / ((2 : ℝ)^n * ((n : ℝ)^4 + 4))
             ) = tsum (fun n0 => term1 n0 + term2 n0 - term3 n0) := by
    -- Use extensionality to show the functions are equal
    have h_ext : (fun n0 =>
                   let n : ℕ := n0 + 2
                   ((n : ℝ)^4 + 3 * (n : ℝ)^2 + 10 * (n : ℝ) + 10) / ((2 : ℝ)^n * ((n : ℝ)^4 + 4))
                 ) = (fun n0 => term1 n0 + term2 n0 - term3 n0) := by
      ext n0
      -- Apply the partial fraction decomposition result
      exact term_rewrite n0

    -- Functions with equal values produce equal sums
    exact congr_arg tsum h_ext

  -- 3. f is non-negative (needed for summability)
  have f_nonneg (k : ℕ) : 0 ≤ f k := by
    unfold f
    -- Establish denominator is positive
    have h_denom_pos : 0 < (2 : ℝ)^k * ((k : ℝ)^2 + 1) := by
      apply mul_pos
      · exact pow_pos (by norm_num) k
      · apply add_pos_of_nonneg_of_pos
        · exact pow_two_nonneg (k : ℝ)
        · norm_num

    -- Since numerator is positive and denominator is positive, the ratio is positive
    apply div_nonneg
    · norm_num
    · exact le_of_lt h_denom_pos

  -- 4. f is summable
  have f_summable : Summable f := by
    -- unfold f
    let g (k : ℕ) := 2 / (2 : ℝ) ^ k
    have g_summable : Summable fun (n : ℕ) => (4 : ℝ) / 2 / 2 ^ n := by
      exact summable_geometric_two' 4

    ring_nf at g_summable

    have hg : Summable g := by
      unfold g
      ring_nf
      exact g_summable

    have hfg : ∀ (b : ℕ), f b ≤ g b := by
      intro b
      unfold f g

      have h2b_pos : (0 : ℝ) < ↑(2 ^ b) := by
        positivity

      apply (div_le_div_iff₀ _ _).mpr
      all_goals
      nlinarith
    exact Summable.of_nonneg_of_le f_nonneg hfg hg


  -- 5. term1 is summable
  have term1_summable : Summable term1 := by
    unfold term1

    -- Rewrite term1 as a scaled geometric series
    have h_rewrite : (fun n0 : ℕ => 1 / (2 : ℝ)^(n0 + 2)) =
                     (fun n0 : ℕ => (1 / (2 : ℝ)^2) * (1 / (2 : ℝ))^n0) := by
      ext
      rw [pow_add]
      ring_nf

    rw [h_rewrite]

    -- Use summability of geometric series
    apply Summable.mul_left

    have r_nonneg : (0 : ℝ) ≤ (1 / (2 : ℝ)) := by norm_num
    have r_lt_one : (1 / (2 : ℝ)) < 1 := by norm_num

    exact summable_geometric_of_lt_one r_nonneg r_lt_one

  -- 6. term2 is summable
  have term2_summable : Summable term2 := by
    unfold term2
    rw [summable_nat_add_iff 1]
    exact f_summable
  -- 7. term3 is summable
  have term3_summable : Summable term3 := by
    unfold term3
    rw [summable_nat_add_iff 3]
    exact f_summable


  have f2_summable : Summable (fun b ↦ f (b + 1 + 1)) := by
    rw [summable_nat_add_iff 2]
    exact f_summable

  -- 8. Linearity of tsum to separate our sum into three parts
  have h2 : tsum (fun n0 => term1 n0 + term2 n0 - term3 n0) = tsum term1 + tsum term2 - tsum term3 := by
    -- First, rewrite (a + b - c) as (a + b) - c
    have h_rewrite : (fun n0 => term1 n0 + term2 n0 - term3 n0) =
                      (fun n0 => (term1 n0 + term2 n0) - term3 n0) := by
      ext
      simp only [add_sub_assoc]

    rw [h_rewrite]

    -- Apply tsum_sub
    have sum_sub : tsum (fun n0 => (term1 n0 + term2 n0) - term3 n0) =
                   tsum (fun n0 => term1 n0 + term2 n0) - tsum term3 := by
      apply tsum_sub
      · have h_add : Summable (fun n0 => term1 n0 + term2 n0) := by
          apply Summable.add term1_summable term2_summable
        exact h_add
      · exact term3_summable

    rw [sum_sub]

    -- Apply tsum_add
    have sum_add : tsum (fun n0 => term1 n0 + term2 n0) = tsum term1 + tsum term2 := by
      apply tsum_add term1_summable term2_summable

    rw [sum_add]

  -- 9. Sum of term1 equals 1/2
  have sum_term1 : tsum term1 = (1 : ℝ)/2 := by
    unfold term1

    have h_rewrite : (fun n0 : ℕ => 1 / (2 : ℝ)^(n0 + 2)) =
                     (fun n0 : ℕ => (1 / (2 : ℝ)^2) * (1 / (2 : ℝ))^n0) := by
      ext
      rw [pow_add]
      ring_nf

    rw [h_rewrite]
    rw [tsum_mul_left]

    have h_r : (0 : ℝ) ≤ (1 / (2 : ℝ)) := by norm_num
    have h_lt : (1 / (2 : ℝ)) < 1 := by norm_num

    rw [tsum_geometric_of_lt_one h_r h_lt]
    norm_num

  -- 10. Telescoping sum of term2 - term3
  have telescope_sum : tsum term2 - tsum term3 = f 1 + f 2 := by
    rw [tsum_eq_zero_add, tsum_eq_zero_add]
    unfold term3
    ring
    apply f2_summable
    exact term2_summable

  -- 11. Value of f(1)
  have f1_val : f 1 = (1 : ℝ)/2 := by
    unfold f
    norm_num

  -- 12. Value of f(2)
  have f2_val : f 2 = (1 : ℝ)/10 := by
    unfold f
    norm_num

  -- 13. Apply lemmas for each sum value
  have h3 : tsum term1 + tsum term2 - tsum term3 = (1 : ℝ)/2 + (f 1 + f 2) := by
    rw [sum_term1, add_sub_assoc, telescope_sum]

  -- 14. Apply values of f(1) and f(2)
  have h4 : (1 : ℝ)/2 + (f 1 + f 2) = (1 : ℝ)/2 + (1 : ℝ)/2 + (1 : ℝ)/10 := by
    rw [f1_val, f2_val]
    simp only [add_assoc]

  -- 15. Final simplification
  have h5 : (1 : ℝ)/2 + (1 : ℝ)/2 + (1 : ℝ)/10 = (11 : ℝ)/10 := by
    linarith

  -- Chain of equalities to reach our conclusion
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
