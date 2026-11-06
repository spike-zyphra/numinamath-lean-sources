import Mathlib

/- Let $x_1 < x_2 < x_3$ be the three real roots of the equation $\sqrt{2014}x^3-4029x^2+2=0$. Find $x_2(x_1+x_3)$. -/
theorem algebra_95962 (x : Fin 3 → ℝ) (hx : ∀ i j, i < j → x i < x j)
    (h : ∀ i, Real.sqrt 2014 * x i ^ 3 - 4029 * x i ^ 2 + 2 = 0) :
    x 1 * (x 0 + x 2) = 2 := by

  -- Note that we can factor the polynomial as a linear times a quadratic.
  have h_factor {y} : √2014 * y ^ 3 - 4029 * y ^ 2 + 2 = (√2014 * y - 1) * (y ^ 2 - 2 * √2014 * y - 2) := by
    ring_nf
    simp
    ring

  -- One root is clearly 1 / √2014. We can solve for the roots using the quadratic formula.
  have h_quadratic_roots {y} : y ^ 2 - 2 * √2014 * y - 2 = 0 ↔ y = √2014 + √2016 ∨ y = √2014 - √2016 := by
    rw [show y ^ 2 - 2 * √2014 * y - 2 = 1 * (y * y) + (-2 * √2014) * y + (-2) by ring]
    have : discrim (R := ℝ) 1 (-2 * √2014) (-2) = (2 * √2016) * (2 * √2016) := by
      simp [discrim, mul_pow]
      move_mul [2]
      move_mul [2]
      norm_num
    rw [quadratic_eq_zero_iff (show (1 : ℝ) ≠ 0 by simp) this y]
    simp
    rw [← mul_add, ← mul_sub]
    simp

  -- Here we list all the roots, and verify that these are indeed roots of the polynomial and are in ascending order.
  let y : Fin 3 → ℝ
  | 0 => √2014 - √2016
  | 1 => 1 / √2014
  | 2 => √2014 + √2016

  have y_roots : ∀ i, √2014 * y i ^ 3 - 4029 * y i ^ 2 + 2 = 0 := by
    intro i
    fin_cases i
    all_goals simp [h_factor]
    . apply Or.inr
      rw [h_quadratic_roots]
      apply Or.inr
      simp [y]
    . apply Or.inl
      simp [y]
    . apply Or.inr
      rw [h_quadratic_roots]
      apply Or.inl
      simp [y]

  have y_mono : StrictMono y := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp at hij
    all_goals simp [y, hij, -one_div]
    . -- y 0 < y 1
      refine lt_trans ?_ (show 0 < 1 / √2014 by simp)
      have : √2014 < √2016 := by rw [← sq_lt_sq₀ (by simp) (by simp)]; norm_num
      linarith
    . -- y 0 < y 2
      rw [sub_eq_add_neg]
      simp
    . -- y 1 < y 2
      refine lt_trans ?_ (show √2014 < √2014 + √2016 by simp)
      rw [div_lt_iff₀ (by norm_num)]
      simp

  -- Now we need to match these roots up with x1, x2, and x3. We do that by
  -- showing that both x and y are order embeddings onto the roots of the degree-3 polynomial
  -- and therefore must cover all of them. Since order embeddings are unique, they must be equal.
  have : x = y := by
    rw [← StrictMono.range_inj hx y_mono]
    let P : Polynomial ℝ := Polynomial.C √2014 * Polynomial.X ^ 3 - Polynomial.C 4029 * Polynomial.X ^ 2 + Polynomial.C 2
    have hPdeg : P.natDegree = 3 := by simp [P]; compute_degree!
    have (a : Fin 3 → ℝ) (hinj : Function.Injective a) (ha : ∀ i, √2014 * a i ^ 3 - 4029 * a i ^ 2 + 2 = 0) : Set.range a = P.rootSet ℝ := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_
      . rw [Set.range_subset_iff]
        intro i
        rw [Polynomial.mem_rootSet_of_ne (Polynomial.ne_zero_of_natDegree_gt (show 0 < P.natDegree by simp [hPdeg]))]
        simp [P]
        exact ha i
      . rw [show (Set.range a).ncard = Nat.card (Set.range a) by rw [Set.Nat.card_coe_set_eq], Nat.card_range_of_injective hinj]
        rw [Polynomial.rootSet_def, Polynomial.aroots_def, Set.ncard_coe_Finset]
        apply le_trans (Multiset.toFinset_card_le _)
        apply le_trans (Polynomial.card_roots' _)
        apply le_trans Polynomial.natDegree_map_le ?_
        simp [hPdeg]
    rw [this x (StrictMono.injective hx) h, this y (StrictMono.injective y_mono) y_roots]

  -- Now we can compute the result.
  rw [this]
  simp [y]
  rw [← mul_two, ← mul_assoc]
  simp