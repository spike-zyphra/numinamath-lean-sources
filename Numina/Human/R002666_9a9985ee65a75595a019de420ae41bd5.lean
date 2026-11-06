import Mathlib

open Set

/- Find the number of integers $c$ such that the equation
$$
\left||20|x|-x^2|-c\right|=21
$$
has $12$ distinct real solutions. -/
theorem algebra_98506 :
    {c : ℤ | {x : ℝ | abs (|20 * |x| - x ^ 2| - (c : ℝ)) = 21}.encard = 12}.ncard = 57 := by
  -- Define solutionOn f s y as the number of solutions of the equation f x = y on the set s
  set solutionsOn : (ℝ → ℝ) → (Set ℝ) → ℝ → ℕ∞ := fun f s y => {x | x ∈ s ∧ f x = y}.encard
  have solutionsOn_preimage {f s y} : solutionsOn f s y = (f⁻¹'{y} ∩ s).encard := by
    dsimp [solutionsOn]; congr
    ext x; simp; exact And.comm
  -- If f x = g x for all x ∈ s then solutionsOn f s y = solutionsOn g s y
  have solutionsOn_congr {f g s y} (hfg : ∀ x ∈ s, f x = g x) : solutionsOn f s y = solutionsOn g s y := by
    dsimp [solutionsOn]
    congr 1
    ext x; simp; intro h
    rw [hfg _ h]
  -- The number of solutions of the equation f x = y on the set s ∪ t plus
  -- the number of solutions of the equation f x = y on the set s ∩ t is
  -- equal to solutionsOn f s y + solutionsOn f t y
  have solutionsOn_union {f s t y} : solutionsOn f (s ∪ t) y + solutionsOn f (s ∩ t) y = solutionsOn f s y + solutionsOn f t y := by
    simp_rw [solutionsOn_preimage]
    rw [inter_union_distrib_left, inter_inter_distrib_left]
    rw [encard_union_add_encard_inter]
  -- If s = ∅ then solutionsOn f ∅ y = 0
  have solutionsOn_empty {f y} : solutionsOn f ∅ y = 0 := by simp [solutionsOn]
  -- If s ∩ t = ∅ then solutionsOn f (s ∪ t) y = solutionsOn f s y + solutionsOn f t y
  have solutionsOn_union_disj {f s t y} (hst : s ∩ t = ∅) : solutionsOn f (s ∪ t) y = solutionsOn f s y + solutionsOn f t y := by
    have := @solutionsOn_union f s t y
    rw [hst, solutionsOn_empty, add_zero] at this
    exact this
  -- If s = {x} then solutionsOn f {x} y = 1 if f x = y and solutionsOn f {x} y = 0 if f x ≠ y
  have solutionsOn_singleton {f x y} : solutionsOn f {x} y = if f x = y then 1 else 0 := by
    dsimp [solutionsOn]
    split_ifs with h
    · rw [encard_eq_one]
      use x; ext v; simp
      intro eq; rw [eq, h]
    · simp
      ext v; simp
      intro eq; simp [eq, h]
  -- If s ⊆ t then solutionsOn f s y ≤ solutionsOn f t y
  have solutionsOn_subset_le {f s t} y (hst : s ⊆ t) : solutionsOn f s y ≤ solutionsOn f t y := by
    simp_rw [solutionsOn_preimage]
    apply encard_le_card
    exact inter_subset_inter (fun ⦃a⦄ a ↦ a) hst
  -- If the function f is injective on s and y is not in the image of s under f
  -- then solutionsOn f s y = 0
  have solutionsOn_Inj0 {f s y} (hf : InjOn f s) (hy : y ∉ f '' s) : solutionsOn f s y = 0 := by
    simp [solutionsOn] at hy ⊢
    intro x a
    simp_all only [inter_empty, encard_empty, implies_true, not_false_eq_true, solutionsOn]
  -- If the function f is injective on s and y is in the image of s under f
  -- then solutionsOn f s y = 1
  have solutionsOn_Inj1 {f s y} (hf : InjOn f s) (hy : y ∈ f '' s) : solutionsOn f s y = 1 := by
    simp [solutionsOn_preimage]
    have eq : f '' (f⁻¹'{y} ∩ s) = {y} := by
      rw [Set.image_preimage_inter]
      simp at hy ⊢
      exact hy
    rw [←InjOn.encard_image (f := f) (s := f⁻¹'{y} ∩ s), eq, encard_singleton]
    apply InjOn.mono _ hf
    simp only [inter_subset_right]
  -- Let f = |20 * |x| - x^2|
  --     f1 = 20 * x - x^2
  --     f2 = x^2 - 20 * x
  set f : ℝ → ℝ := fun x => |20 * |x| - x^2|
  set f1 : ℝ → ℝ := fun x => 20 * x - x ^ 2
  set f2 : ℝ → ℝ := fun x => x ^ 2 - 20 * x
  -- The function f is even: f (-x) = f x
  have hf_even x : f (-x) = f x := by simp [f]
  have f1_cont : Continuous f1 := by fun_prop
  have f2_cont : Continuous f2 := by fun_prop
  -- 0 ≤ f1 x iff x ∈ [0, 20]
  have f1_nonneg : ∀ x, 0 ≤ f1 x ↔ x ∈ Icc 0 20 := by
    intro x
    -- f1 x = x * (20 - x), so f1 x ≥ 0 iff 0 ≤ x ≤ 20
    simp only [mem_Icc, f1, show 20 * x - x ^ 2 = x * (20 - x) by ring, mul_nonneg_iff]
    simp_rw [show ¬ (x ≤ 0 ∧ 20 - x ≤ 0) by by_contra!; linarith]
    simp only [sub_nonneg, or_false]
  -- If 0 ≤ x then 0 < f2 x iff x ∈ (20, ∞)
  have f2_pos {x} (hx : 0 ≤ x) : 0 < f2 x ↔ x ∈ Ioi 20 := by
    simp [show f2 x = -f1 x by simp [f1, f2]]
    contrapose! f1_nonneg
    use x
    simp only [mem_Icc, not_and, not_le]
    tauto
  -- If x ∈ [0, 20] then f x = f1 x (because x ≥ 0 and 20 * x - x^2 ≥ 0)
  have f_eq_f1 : ∀ x ∈ Icc 0 20, f x = f1 x := by
    intro x hx
    simp_rw [f, f1, abs_of_nonneg (show 0 ≤ x by simp at hx; linarith)]
    rw [abs_of_nonneg ((f1_nonneg x).mpr hx)]
  -- If x ∈ (20, ∞) then f x = f2 x (because x ≥ 0 and x^2 - 20 * x > 0)
  have f_eq_f2 : ∀ x ∈ Ioi 20, f x = f2 x := by
    intro x hx
    have hx0 : 0 ≤ x := by simp at hx; linarith
    simp_rw [f, f2, abs_of_nonneg hx0]
    rw [abs_sub_comm, abs_of_pos ((f2_pos hx0).mpr hx)]
  -- The number of solutions of the equation f x = y on the set [0, ∞) is equal to
  -- solutionsOn f1 [0, 10] y + solutionsOn f1 (10, 20] y + solutionsOn f2 (20, ∞) y
  have hf_nonneg y : solutionsOn f (Ici 0) y =
      solutionsOn f1 (Icc 0 10) y + solutionsOn f1 (Ioc 10 20) y + solutionsOn f2 (Ioi 20) y := by
    -- We have [0, ∞) = [0, 10] ∪ (10, 20] ∪ (20, ∞)
    have eq : Ici (0 : ℝ) = Icc 0 10 ∪ Ioc 10 20 ∪ Ioi 20 := by
      rw [Icc_union_Ioc_eq_Icc (by norm_num) (by norm_num)]
      rw [Icc_union_Ioi_eq_Ici (by norm_num)]
    -- [0, 10] and (10, 20] are disjoint
    have disj1 : Icc (0 : ℝ) 10 ∩ Ioc 10 20 = ∅ := by ext x; simp; intros; linarith
    -- ([0, 10] ∪ (10, 20]) and (20, ∞) are disjoint
    have disj2 : (Icc (0 : ℝ) 10 ∪ Ioc 10 20) ∩ Ioi 20 = ∅ := by
      ext x; simp; intro h; cases h <;> linarith
    -- Rewrite solutionsOn f [0, ∞) y as the sum of
    -- solutionsOn f [0, 10] y + solutionsOn f (10, 20] y + solutionsOn f (20, ∞) y
    rw [eq, solutionsOn_union_disj disj2, solutionsOn_union_disj disj1]
    -- f x = f1 x for x ∈ [0, 10] so solutionsOn f [0, 10] y = solutionsOn f1 [0, 10] y
    have h1 : solutionsOn f (Icc 0 10) y = solutionsOn f1 (Icc 0 10) y := by
      apply solutionsOn_congr
      intro x hx
      apply f_eq_f1
      simp at hx ⊢; constructor <;> linarith
    -- f x = f1 x for x ∈ (10, 20] so solutionsOn f (10, 20] y = solutionsOn f1 (10, 20] y
    have h2 : solutionsOn f (Ioc 10 20) y = solutionsOn f1 (Ioc 10 20) y := by
      apply solutionsOn_congr
      intro x hx
      apply f_eq_f1
      simp at hx ⊢; constructor <;> linarith
    -- f x = f2 x for x > 20 so solutionsOn f (20, ∞) y = solutionsOn f2 (20, ∞) y
    have h3 : solutionsOn f (Ioi 20) y = solutionsOn f2 (Ioi 20) y := by
      apply solutionsOn_congr
      intro x hx
      apply f_eq_f2 _ hx
    rw [h1, h2, h3]
  -- solutionsOn f1 [0, 10] y = 1 if 0 ≤ y ≤ 100 and 0 for other values of y
  have hf1 y : solutionsOn f1 (Icc 0 10) y = if 0 ≤ y ∧ y ≤ 100 then 1 else 0 := by
    -- Show that f1 is injective on [0, 10]
    have hinj : InjOn f1 (Icc 0 10) := by
      simp [InjOn, f1]
      intro x hx1 hx2 y hy1 hy2 eq
      -- f1 x = f1 y implies that (x - y) * (x + y - 20) = 0
      -- so x = y or x + y = 20. The second case is possible for x = y = 10 only.
      replace eq : (x - y) * (x + y - 20) = 0 := by linear_combination -eq
      rw [mul_eq_zero] at eq
      cases' eq with h h <;> linarith
    split_ifs with hy
    -- Suppose that 0 ≤ y ≤ 100 and show that solutionsOn f1 [0, 10] y = 1.
    -- We need to show that y ∈ f1 '' [0, 10].
    · apply solutionsOn_Inj1 hinj
      -- We have [f1 0, f1 10] ⊆ f1 '' [0, 10] by the intermediate value theorem
      have hs := intermediate_value_Icc (show (0 : ℝ) ≤ 10 by norm_num) f1_cont.continuousOn
      -- It is easy to show that y ∈ [f1 0, f1 10] = [0, 100]
      apply Set.mem_of_subset_of_mem hs
      simp only [mem_Ioc, f1]
      norm_num [hy]
    -- Suppose that ¬ (0 ≤ y ≤ 100) and show that solutionsOn f1 [0, 10] y = 0.
    -- We need to show that y ∉ f1 '' [0, 10]
    · apply solutionsOn_Inj0 hinj
      simp only [not_and, not_le, mem_image, mem_Icc, not_exists, and_imp, f1] at hy ⊢
      intro x hx1 hx2
      by_cases h : 0 ≤ y
      -- Assume that 100 < y and show that f1 x = 20 * x - x ^ 2 ≤ 100 < y for x ∈ [0, 10]
      · apply ne_of_lt
        suffices 20 * x - x ^ 2 ≤ 100 by linarith [hy h]
        nlinarith
      -- Assume that y < 0 and show that f1 x = 20 * x - x ^ 2 ≥ 0 > y for x ∈ [0, 10]
      · contrapose! h
        rw [←h, show 20 * x - x ^ 2 = x * (20 - x) by ring]
        nlinarith
  -- solutionsOn f1 (10, 20] y = 1 if 0 ≤ y < 100 and 0 for other values of y
  have hf2 y : solutionsOn f1 (Ioc 10 20) y = if 0 ≤ y ∧ y < 100 then 1 else 0 := by
    -- Show that f1 is injective on (10, 20]
    have hinj : InjOn f1 (Ioc 10 20) := by
      simp [InjOn, f1]
      intro x hx1 hx2 y hy1 hy2 eq
      -- f1 x = f1 y implies that (x - y) * (x + y - 20) = 0
      -- so x = y or x + y = 20. The second case is impossible since x > 10 and y > 10.
      replace eq : (x - y) * (x + y - 20) = 0 := by linear_combination -eq
      rw [mul_eq_zero] at eq
      cases' eq with h h <;> linarith
    split_ifs with hy
    -- Suppose that 0 ≤ y < 100 and show that solutionsOn f1 (10, 20] y = 1.
    -- We need to show that y ∈ f1 '' (10, 20].
    · apply solutionsOn_Inj1 hinj
      -- We have [f1 20, f1 10) ⊆ f1 '' (10, 20] by the intermediate value theorem
      have hs := intermediate_value_Ioc' (show (10 : ℝ) ≤ 20 by norm_num) f1_cont.continuousOn
      -- It is easy to show that y ∈ [f1 20, f1 10) = [0, 100)
      apply Set.mem_of_subset_of_mem hs
      simp only [mem_Ioc, f1]
      norm_num [hy]
    -- Suppose that ¬ (0 ≤ y < 100) and show that solutionsOn f1 (10, 20] y = 0.
    -- We need to show that y ∉ f1 '' (10, 20]
    · apply solutionsOn_Inj0 hinj
      simp [f1] at hy ⊢
      intro x hx1 hx2
      by_cases h : 0 ≤ y
      -- Assume that 100 ≤ y and show that f1 x = 20 * x - x ^ 2 < 100 ≤ y for x ∈ (10, 20]
      · apply ne_of_lt
        suffices 20 * x - x ^ 2 < 100 by linarith [hy h]
        nlinarith
      -- Assume that y < 0 and show that f1 x = 20 * x - x ^ 2 ≥ 0 > y for x ∈ (10, 20]
      · contrapose! h
        rw [←h, show 20 * x - x ^ 2 = x * (20 - x) by ring]
        nlinarith
  -- solutionsOn f2 (20, ∞) y = 1 if 0 < y and 0 for other values of y
  have hf3 y : solutionsOn f2 (Ioi 20) y = if 0 < y then 1 else 0 := by
    -- Show that f2 is injective on (20, ∞)
    have hinj : InjOn f2 (Ioi 20) := by
      simp [InjOn, f2]
      intro x hx y hy eq
      -- f2 x = f2 y implies that (x - y) * (x + y - 20) = 0
      -- so x = y or x + y = 20. The second case is impossible since x > 20 and y > 20.
      replace eq : (x - y) * (x + y - 20) = 0 := by linear_combination eq
      simp [mul_eq_zero, show ¬ x + y - 20 = 0 by linarith] at eq
      linarith
    split_ifs with hy
    -- Suppose that 0 < y and show that solutionsOn f2 (20, ∞) y = 1.
    -- We need to show that y ∈ f2 '' (20, ∞).
    · apply solutionsOn_Inj1 hinj
      -- We have f2 '' (20, y + 20] ⊆ f2 '' (20, ∞)
      have hs : f2 '' Set.Ioc 20 (y + 20) ⊆ f2 '' Ioi 20 := by
        apply Set.image_subset
        exact Ioc_subset_Ioi_self
      apply Set.mem_of_subset_of_mem hs
      -- We have (f2 20, f2 (y + 20)] ⊆ f2 '' (20, y + 20] by the intermediate value theorem
      have hs2 := intermediate_value_Ioc (show 20 ≤ y + 20 by linarith) f2_cont.continuousOn
      apply Set.mem_of_subset_of_mem hs2
      -- Show that y ∈ (f2 20, f2 (y + 20)] = (0, (y + 20) ^ 2 - 20 * (y + 20)]
      simp only [mem_Ioc, f2]
      norm_num [hy]
      nlinarith
    -- Suppose that y ≤ 0 and show that solutionsOn f2 (20, ∞) y = 0.
    -- We need to show that y ∉ f2 '' (20, ∞).
    · apply solutionsOn_Inj0 hinj
      simp [f2] at hy ⊢
      intro x hx
      -- We have y ≤ 0 < x ^ 2 - 20 * x = f2 x for x > 20.
      apply ne_of_gt
      apply lt_of_le_of_lt hy
      nlinarith
  -- The function f is even so we can prove that
  -- solutionsOn f ℝ y = 2 * solutionsOn f [0, ∞) y - (if y = 0 then 1 else 0)
  have hf_sol y : solutionsOn f univ y = 2 * solutionsOn f (Ici 0) y - if y = 0 then 1 else 0 := by
    -- We have ℝ = (-∞, 0] ∪ [0, ∞).
    rw [(Iic_union_Ici (a := 0)).symm]
    -- The number of solutions of f x = y on (-∞, 0] ∩ [0, ∞) = {0} is 1 if y = 0 and 0 otherwise.
    have eq : solutionsOn f (Iic 0 ∩ Ici 0) y = if y = 0 then 1 else 0 := by
      suffices Iic 0 ∩ Ici 0 = {(0 : ℝ)} by simp [this, solutionsOn_singleton, f, eq_comm]
      ext x
      simp [le_antisymm_iff]
    rw [←eq, eq_comm]
    rw [AddLECancellable.tsub_eq_iff_eq_add_of_le]
    rotate_left
    · apply ENat.addLECancellable_of_ne_top
      rw [eq]
      norm_cast
      exact ENat.coe_ne_top _
    · rw [two_mul, ←add_zero (solutionsOn _ _ _)]
      apply add_le_add _ (zero_le _)
      apply solutionsOn_subset_le
      simp only [inter_subset_right]
    -- We have solutionOn f ((-∞, 0] ∪ [0, ∞)) y + solutionsOn f ((-∞, 0] ∩ [0, ∞)) y = solutionsOn f (-∞, 0] y + solutionsOn f [0, ∞) y.
    rw [solutionsOn_union]
    -- It is left to show that solutionsOn f (-∞, 0] y = solutionsOn f [0, ∞) y.
    suffices solutionsOn f (Iic 0) y = solutionsOn f (Ici 0) y by rw [this, two_mul]
    dsimp [solutionsOn]
    -- The result follows from the fact that f (-x) = f x.
    suffices (-·) '' {x | x ∈ Ici 0 ∧ f x = y} = {x | x ∈ Iic 0 ∧ f x = y} by
      rw [←this, Function.Injective.encard_image]
      intro x y
      simp only [neg_inj, imp_self]
    ext x
    simp [hf_even]
  -- Find the number of values of c ∈ ℤ such that ||20 * |x| - x ^2| - c| = 21 has exactly 12 solutions.
  calc
    -- Show that ||20 * |x| - x ^2| - c| = 21 has exactly 12 solutions iff
    -- solutionsOn f ℝ (c - 21) + solutionsOn f ℝ (c + 21) = 12.
    {c : ℤ | {x : ℝ | abs (|20 * |x| - x ^ 2| - (c : ℝ)) = 21}.encard = 12}.ncard =
      {c : ℤ | solutionsOn f univ (c - 21) + solutionsOn f univ (c + 21) = 12}.ncard := by
        congr
        ext c; simp [solutionsOn]
        -- Let s be the set of solutions of |f x - c| = 21 for a fixed c.
        set s := {x | _}
        -- Let t be the set of solutions of f x = c - 21 for a fixed c.
        set t := {x | _}
        -- Let r be the set of solutions of f x = c + 21 for a fixed c.
        set r := {x | _}
        -- It is enough to show that s = t ∪ r and t ∩ r = ∅.
        suffices s = t ∪ r ∧ t ∩ r = ∅ by
          rw [this.1, encard_union_eq]
          rw [disjoint_iff_inter_eq_empty]
          exact this.2
        constructor
        -- t ∪ r = s because |f x - c| = 21 iff f x = c - 21 or f x = c + 21
        · ext x
          simp [s, t, r, f]
          rw [abs_eq (by norm_num), sub_eq_iff_eq_add, sub_eq_iff_eq_add]
          rw [add_comm, add_comm (-21), show (c : ℝ) + -21 = c - 21 by ring, Or.comm]
        -- t ∩ r = ∅ because equations f x = c - 21 and f x = c + 21 have no common solutions.
        · ext x
          simp [t, r]
          intro eq
          rw [eq]
          linarith
    -- Now show that solutionsOn f ℝ (c - 21) + solutionsOn f ℝ (c + 21) = 12 iff c ∈ (21, 79)
    _ = (Finset.Ioo (21 : ℤ) 79).card := by
        suffices  {c : ℤ | solutionsOn f univ (↑c - 21) + solutionsOn f univ (↑c + 21) = 12} = Finset.Ioo (21 : ℤ) 79 by
          rw [this, ncard_coe_Finset]
        ext c
        -- We proved that solutionsOn f ℝ y = 2 * solutionsOn f [0, ∞) y - (if y = 0 then 1 else 0)
        --      = 2 * (solutionsOn f1 [0, 10] y + solutionsOn f1 (10, 20] y + solutionsOn f2 (20, ∞) y) - (if y = 0 then 1 else 0)
        --      = 2 * ((if 0 ≤ y ≤ 100 then 1 else 0) + (if 0 ≤ y < 100 then 1 else 0) + (if 0 < y then 1 else 0)) - (if y = 0 then 1 else 0).
        -- We need to find all values of c such that solutionsOn f ℝ (c - 21) + solutionsOn f ℝ (c + 21) = 12.
        simp [hf_sol, hf_nonneg, hf1, hf2, hf3]
        constructor
        -- Suppose that the number of solutions is 12 and show that c ∈ (21, 79).
        -- Consider 5 cases: c < 21, c = 21, c ∈ (21, 79), c = 79, and 79 < c.
        · rcases show c < 21 ∨ c = 21 ∨ 21 < c ∧ c < 79 ∨ c = 79 ∨ 79 < c by omega with hc | hc | hc | hc | hc
          -- If c < 21 then it follows that the number of solutions is less than 12.
          · rify at hc
            simp [show ¬ 21 ≤ (c : ℝ) by linarith, show ¬ 21 < (c : ℝ) by linarith]
            simp [show ¬ (c : ℝ) - 21 = 0 by linarith]
            set r := ((2 : ℕ∞) * _) - _
            suffices r ≤ 2 * ((1 + 1) + 1) - 0 by
              intro eq
              rw [eq] at this
              contradiction
            dsimp [r]
            clear * -
            gcongr <;> split_ifs <;> simp only [le_refl, zero_le]
          -- If c = 21 then the number of solutions is 9 < 12
          · rify at hc
            simp [hc]
            intro h
            norm_cast at h
          -- If c ∈ (21, 79) then the result follows.
          · exact fun _ => hc
          -- If c = 79 then the number of solutions is 10 < 12
          · rify at hc
            simp [hc]
            intro h
            norm_cast at h
          -- If 79 < c then it follows that the number of solutions is less than 12.
          · rify at hc
            simp [show ¬ (c : ℝ) + 21 = 0 by linarith, show ¬ (c : ℝ) - 21 = 0 by linarith]
            simp [show 0 < (c : ℝ) + 21 by linarith, show ¬ (c : ℝ) + 21 ≤ 100 by linarith]
            simp [show 21 < (c : ℝ) by linarith, show ¬ (c : ℝ) + 21 < 100 by linarith]
            set r := ((2 : ℕ∞) * _) + _
            suffices r ≤ 2 * ((1 + 1) + 1) + 2 by
              intro eq
              rw [eq] at this
              contradiction
            dsimp [r]
            clear * -
            gcongr <;> split_ifs <;> simp only [le_refl, zero_le]
        -- Suppose that c ∈ (21, 79) and show that the number of solutions is 12.
        · intro hc
          rify at hc
          -- Count all solutions
          simp [hc, show 21 ≤ (c : ℝ) by linarith, show (c : ℝ) ≤ 100 + 21 by linarith]
          simp [show (c : ℝ) - 21 < 100 by linarith, show 0 ≤ (c : ℝ) + 21 by linarith]
          simp [show (c : ℝ) + 21 < 100 by linarith, show (c : ℝ) + 21 ≤ 100 by linarith]
          simp [show 0 < (c : ℝ) + 21 by linarith, show (c : ℝ) - 21 ≠ 0 by linarith]
          simp [show (c : ℝ) + 21 ≠ 0 by linarith]
          norm_num
    -- The number of elements in the set (21, 79) is 57.
    _ = 57 := by simp