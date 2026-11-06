import Mathlib

open Real

/- AM-GM inequality variant for a finite number of real non-negative variables. -/
lemma Fin_geom_mean_le_arith_mean {n : ℕ} [NeZero n]
  {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
  : n * (∏ j, a j) ^ (1 / n : ℝ) ≤ ∑ j, a j := by

    -- apply AM-GM to a, where equal weights of (1 / n)
    have am_gm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 / n : ℝ)) a
      (fun _ _ => Nat.one_div_cast_nonneg n) (by norm_num) (fun i a => ha i)

    -- the weights sum to 1
    have weights_sum_one : (∑ i : Fin n, (fun x => (1 / n : ℝ)) i) = 1 := by norm_num

    -- simplify AM-GM
    norm_num [weights_sum_one, ←Finset.mul_sum] at am_gm

    -- n is positive
    have n_pos : (0 : ℝ) < n := by norm_num [Nat.pos_of_neZero n]

    -- multiply both sides by n
    replace am_gm := (mul_le_mul_left n_pos).mpr am_gm

    -- we have the desired inequality
    convert am_gm
    -- lhs is equal
    -- power distributes over product
    · rw [Real.finset_prod_rpow]
      norm_num
      · norm_num [ha]
    -- rhs is equal
    · field_simp

/- AM-GM inequality variant for a finite number of real non-negative variables.
  Given n variables a_i, we have
  n ^ n * (∏ a j) ≤ (∑ a j) ^ n
-/
lemma Fin_pow_mul_prod_le_sum_pow {n : ℕ} [NeZero n]
  {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
  : n ^ n * (∏ j, a j) ≤ (∑ j, a j) ^ n := by
    -- use AM-GM to get
    --  n * (∏ a j) ^ (1 / n) ≤ ∑ a j
    have am_gm := Fin_geom_mean_le_arith_mean ha
    -- the product is positive
    have prod_pos : 0 ≤ ∏ j : Fin n, a j := Finset.prod_nonneg fun i a => ha i
    -- the product to the power of 1 / n is positive
    have prod_pow_pos : 0 ≤ (∏ j : Fin n, a j) ^ (1 / n : ℝ) := rpow_nonneg prod_pos (1 / n)
    -- n is non-negative
    have n_pos : (0 : ℝ) ≤ n := by positivity

    -- take each side of the inequality to the power of n
    have powed := pow_le_pow_left₀ (by positivity) am_gm n

    -- simplify
    rw [←Real.rpow_natCast, Real.mul_rpow (by positivity) prod_pow_pos, ←Real.rpow_mul prod_pos] at powed
    norm_num at powed

    -- we're done
    exact powed

/- Telescoping product for positive real numbers. -/
lemma Real_prod_succ_div_of_nonneg {f : ℕ → ℝ} (h : ∀ i, 0 < f i)
  : ∏ x ∈ Finset.range n, f (x + 1) / f x = f n / f 0 := by
    -- note that f(0) is not zero
    have nn_ne : f 0 ≠ 0 := ne_of_gt <| h 0

    -- we prove by induction, checking ratios of consecutive terms
    refine Finset.prod_range_induction _ (fun {n} => f n / f 0) ?_ ?_ n
    · norm_num
      field_simp
    · intro nn
      have nn_ne : f nn ≠ 0 := ne_of_gt <| h nn
      field_simp
      ring


/- Let $a_{2}, \ldots, a_{n}$ be positive real numbers whose product is 1. Show that


$$

\left(1+a_{2}\right)^{2}\left(1+a_{3}\right)^{3} \cdots\left(1+a_{n}\right)^{n} \geqslant n^{n}

$$


## - Solution of exercises - -/
theorem inequalities_156758 (n : ℕ) (a : Fin n → ℝ)
    (h₀ : ∀ i, 0 < a i) (h₁ : ∏ i, a i = 1) :
    ∏ i, (1 + a i) ^ (i + 2 : ℕ) ≥ (n + 1) ^ (n + 1) := by

    -- use ≤ instead of ≥
    simp only [ge_iff_le]

    -- we have a bound on each term of the product
    -- (i + 2) ^ (i + 2) * (1 / ((i + 1) ^ (i + 1))) * a_i ≤ (1 + a_i) ^ (i + 2)
    have bound : ∀ i : Fin n, (i + 2 : ℕ) ^ (i + 2 : ℕ) * (1 / ((i + 1) ^ (i + 1 : ℕ))) * a i ≤ (1 + a i) ^ (i + 2 : ℕ) := by
      intro i
      -- split up the term
      -- (a_i + 1) = a_i + 1 / (i + 1) + 1 / (i + 1) + ... + 1 / (i + 1)
      let f' : Fin (i + 2) → ℝ  := Fin.cons (a i) (fun _ => (1 / (i + 1)))
      have sum_eq : 1 + a i = ∑ i, f' i := by
        unfold f'
        field_simp
        ring
      rw [sum_eq]

      -- each of the RHS terms are non-negative
      have f'_pos : ∀ i, 0 ≤ f' i := by
        intro i
        unfold f'
        -- first term (a_i) is different from the rest
        cases' i using Fin.cases with ii
        · norm_num
          exact le_of_lt <| h₀ i
        · norm_num
          positivity

      -- so we apply AM-GM to get our bound
      convert Fin_pow_mul_prod_le_sum_pow f'_pos using 1
      · norm_num [f', Fin.prod_cons]
        field_simp

    -- so we prove the inequality using the product ∏ i, (i + 2) ^ (i + 2) * (1 / ((i + 1) ^ (i + 1))) * a i
    trans ∏ i : Fin n, (i + 2 : ℕ) ^ (i + 2 : ℕ) * (1 / ((i + 1) ^ (i + 1 : ℕ))) * a i
    -- separate a_i factors, as they multiply together to 1
    · rw [Finset.prod_mul_distrib, h₁]
      norm_num

      -- turn product into a product over a "range" of numbers
      convert_to (n + 1: ℝ) ^ (n + 1) ≤ ∏ x : Fin n, (fun i : ℕ => ((i + 2) ^ (i + 2) * ((i + 1) ^ (i + 1) : ℝ)⁻¹)) x
      rw [←Finset.prod_range (fun i : ℕ => ((i + 2) ^ (i + 2) * ((i + 1) ^ (i + 1) : ℝ)⁻¹))]


      -- make it clear that the product is a telescoping product
      let f : ℕ → ℝ := fun i => (i + 1) ^ (i + 1)
      convert_to (n + 1: ℝ) ^ (n + 1) ≤ ∏ x ∈ Finset.range n, (f (x + 1) / f x)
      · unfold f
        congr
        ext i
        field_simp
        ring

      -- simplify the product using telescoping
      rw [Real_prod_succ_div_of_nonneg]
      norm_num [f]

      -- we used that each term of f is positive
      · intro i
        positivity
    -- we apply the bound we derived for each term
    · refine Finset.prod_le_prod ?_ fun i a => bound i
      -- and we can apply bounds on each term, because every term is non-negative
      intro i hi
      -- recall that a_i is positive
      have ai_pos : 0 < a i := h₀ i
      -- so each term is non-negative
      positivity