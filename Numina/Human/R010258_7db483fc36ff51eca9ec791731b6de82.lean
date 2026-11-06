import Mathlib

open Finset

/- $2 \cdot 55$ Given 1991 distinct positive real numbers, the product of any 10 of them is greater than 1, prove that the product of all 1991 numbers is greater than 1. -/
theorem number_theory_99267 (s : Finset ℝ) (h₀ : s.card = 1991)
    (h₁ : ∀ x ⊆ s, x.card = 10 → ∏ i ∈ x, i > 1)
    (h₂ : ∀ x ∈ s, x > 0) :
    ∏ i ∈ s, i > 1 := by
  have hs_nonempty : s.Nonempty := by simp [←card_pos, h₀]
  -- let a be the maximum of s
  have ⟨a, ha⟩ := max_of_nonempty hs_nonempty
  -- let t = s \ {a}
  set t := s \ {a} with t_eq
  have has : a ∈ s := mem_of_max ha
  have hts : t ⊆ s := sdiff_subset
  -- the cardinality of t is 1991 - 1 = 1990
  have ht_card : t.card = 1990 := by
    dsimp [t]
    rw [card_sdiff, h₀, card_singleton]
    simpa
  -- show that elements of t can be enumerated
  have ⟨f, hft⟩ : ∃ f : ℕ → ℝ, t = (range 1990).image f := by
    -- take a function which returns the i-th element of the list corresponding to t
    use fun i => if h : i < t.toList.length then t.toList[i] else default
    ext x
    simp [ht_card]
    constructor
    · rw [←mem_toList, List.mem_iff_getElem]
      intro ⟨i, hi, hx⟩
      use i
      simp [ht_card] at hi ⊢
      simpa [hi]
    · intro ⟨i, hin, hx⟩
      simp only [← hx, hin, ↓reduceDIte, ← mem_toList, List.getElem_mem]
  -- the function f is injective on [0, 1990)
  have hf_inj : Set.InjOn f (range 1990) := by
    apply injOn_of_card_image_eq
    simp [←hft, ht_card]
  -- define g(i) = [10 * i, 10 * i + 10)
  set g : ℕ → Finset ℝ := fun i => (Ico (10 * i) (10 * i + 10)).image f
  have hsub {i} (hi : i < 199) : Ico (10 * i) (10 * i + 10) ⊆ range 1990 := by
    intro j
    simp only [mem_Ico, mem_range, and_imp]
    omega
  have hsub' {i} (hi : i < 199) : Set.Ico (10 * i) (10 * i + 10) ⊆ Set.Iio 1990 := by
    intro j
    simp only [Set.mem_Ico, Set.mem_Iio, and_imp]
    omega
  have hfg_inj {i} (hi : i < 199) : Set.InjOn f (Ico (10 * i) (10 * i + 10)) := by
    apply Set.InjOn.mono _ hf_inj
    simp only [coe_Ico, coe_range]
    exact hsub' hi
  -- we have #g(i) = 10 for all i < 199
  have hg10 {i} (hi : i < 199) : (g i).card = 10 := by
    rw [show 10 = (Ico (10 * i) (10 * i + 10)).card by simp]
    exact card_image_of_injOn (hfg_inj hi)
  -- we have g(i) ⊆ s for all i < 199
  have hg_sub {i} (hi : i < 199) : g i ⊆ s := by
    apply Subset.trans _ hts
    simp_rw [g, hft]
    exact image_subset_image (hsub hi)
  have hg_prod {i} (hi : i < 199) : ∏ x ∈ g i, x = ∏ j ∈ Ico (10 * i) (10 * i + 10), f j := by
    simp_rw [g, prod_image (hfg_inj hi)]
  -- show that 1 < a
  have ha1 : 1 < a := by
    -- suppose that a ≤ 1 and show that there is a 10-element subset r of s
    -- such that ∏ x ∈ r, x ≤ 1
    contrapose! h₁
    -- take r = g 0 = f [0, 10)
    use g 0
    have h0 : 0 < 199 := by norm_num
    refine ⟨hg_sub h0, hg10 h0, ?_⟩
    -- show that ∏ x ∈ g 0, x ≤ ∏ x ∈ g 0, 1 = 1
    rw [←prod_const_one (s := g 0)]
    apply prod_le_prod
    · intro x hx
      apply le_of_lt
      apply h₂
      exact hg_sub h0 hx
    · intro x hx
      -- we need to show that x ∈ g 0 implies that x ≤ 1
      -- it follows from the assumption a ≤ 1 and from the fact that
      -- a is the maximum of all elements of s
      apply le_trans _ h₁
      apply Finset.le_max_of_eq _ ha
      exact hg_sub h0 hx
  -- rewrite the product as follows
  -- ∏ x ∈ s, x = a * ∏ x ∈ t, x
  rw [Finset.prod_eq_mul_prod_diff_singleton has, ←t_eq]
  -- show that
  -- ∏ x ∈ t, x = ∏ i ∈ [0, 199), (∏ x ∈ g i, x)
  have heq : ∏ i ∈ range 199, ∏ x ∈ g i, x = ∏ x ∈ t, x := calc
    ∏ i ∈ range 199, ∏ x ∈ g i, x = ∏ i ∈ range 199, ∏ j ∈ Ico (10 * i) (10 * i + 10), f j := by
        apply prod_congr rfl
        simp only [mem_range]
        intro i hi
        rw [hg_prod hi]
    _ = ∏ x ∈ t, x  := by
        rw [hft, ←Finset.prod_disjiUnion]
        rotate_left
        -- show that [10 * i, 10 * i + 10) and [10 * j, 10 * j + 10) are disjoint for i ≠ j
        · intro i
          simp only [Finset.coe_range, Set.mem_Iio, ne_eq]
          intro hi j hj hij
          simp only [Function.onFun, Finset.disjoint_iff_ne, Finset.mem_Ico, ne_eq, and_imp]
          omega
        · simp [Finset.prod_image hf_inj]
          apply Finset.prod_congr _ (by simp)
          -- show that the union of intervals [10 * i, 10 * i + 10) for all i < 199
          -- is equal to [0, 1990)
          ext k
          simp
          constructor
          · intro ⟨a, ha⟩
            omega
          · intro hk
            use k / 10
            omega
  rw [←heq]
  apply one_lt_mul (le_of_lt ha1)
  -- we have 1 < a and it is left to show that 1 < ∏ i ∈ [0, 199), (∏ x ∈ g i, x)
  calc
    1 = ∏ i ∈ range 199, 1 := prod_const_one.symm
    _ < ∏ i ∈ range 199, ∏ x ∈ g i, x := by
        apply prod_lt_prod (fun _ _ => zero_lt_one)
        -- show that 1 ≤ ∏ x ∈ g i, x for all i < 199
        -- it follows from h₁ since g i ⊆ s and #(g i) = 10
        · simp only [mem_range]
          intro i hi
          apply le_of_lt
          exact h₁ _ (hg_sub hi) (hg10 hi)
        -- show that 1 < ∏ x ∈ g i, x for some i < 199
        -- it follows from h₁ since g 0 ⊆ s and #(g 0) = 10
        · use 0
          simp only [mem_range, Nat.ofNat_pos, true_and]
          exact h₁ _ (hg_sub (by norm_num)) (hg10 (by norm_num))