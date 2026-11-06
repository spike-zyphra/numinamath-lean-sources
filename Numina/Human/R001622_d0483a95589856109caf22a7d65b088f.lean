import Mathlib

open Finset
set_option maxRecDepth 1000

/- If the total number of eliminated factors are less than 2016, by the PIE, there exists a common factor which is not eliminated. -/
lemma sdiff_non_empty_of_card_add_card_le_2016 {elim_left elim_right : Finset (Fin 2016)} (hcard : elim_left.card + elim_right.card < 2016) :
    ((univ \ elim_left) ∩ (univ \ elim_right)).Nonempty := by
  have huniv : #(univ : Finset (Fin 2016)) = 2016 := by
    rw [card_univ, Fintype.card_fin]
  apply inter_nonempty_of_card_lt_card_add_card (s := univ)
  · simp
  · simp
  · rw [card_sdiff, card_sdiff, huniv]
    · apply Nat.cast_lt (α := ℤ) |>.mp
      simp
      rw [Nat.cast_sub (by nth_rw 2 [←huniv]; apply card_le_card; simp)]
      rw [Nat.cast_sub (by nth_rw 2 [←huniv]; apply card_le_card; simp)]
      apply sub_pos.mp
      ring_nf
      apply Nat.cast_lt (α := ℤ) |>.mpr at hcard
      simp at hcard
      apply sub_pos.mpr at hcard
      ring_nf at hcard
      exact hcard
    · simp
    · simp

/- We count the number of factors in 1 ... 2016 such that i ≡ k [mod 4] for some k. -/
lemma card_filter_mod_eq {k : ℕ} : (univ.filter (fun i : Fin 2016 => (i.val + 1) % 4 = k % 4)).card = 504 := by
  have h : (Icc 0 503).card = 504 := by simp
  rw [←h]
  symm
  have h_lt {i : ℕ} (hi : i ∈ Icc 0 503) : i * 4 + (k + 3) % 4 < 2016 := by
    apply lt_of_le_of_lt (b := 503 * 4 + 3)
    · gcongr
      · simp at hi
        exact hi
      · apply Nat.le_of_lt_succ
        apply Nat.mod_lt
        simp
    · simp
  let inj (i : ℕ) (hi : i ∈ Icc 0 503) : Fin 2016 := ⟨i * 4 + (k + 3) % 4, h_lt hi⟩
  apply card_bij inj
  · intro x hx
    simp [inj]
    simp [Nat.add_mod]
    rw [Nat.mod_mod, Nat.mod_mod, ←Nat.add_mod]
    simp [add_assoc]
  · intro x₁ hx₁ x₂ hx₂ h
    simp [inj] at h
    exact h
  · intro i hi
    use i.val / 4
    constructor
    · simp [inj]
      apply Fin.eq_of_val_eq
      simp at hi ⊢
      have : (k + 3) % 4 = i.val % 4 := by
        rw [Nat.add_mod, ←hi, ←Nat.add_mod]
        simp [add_assoc]
      rw [this]
      exact Nat.div_add_mod' (↑i) 4
    · simp
      trans 2015 / 4
      · gcongr
        apply Nat.le_of_lt_succ
        exact i.2
      · simp

/- Show that the production can be rewrited as ∏ i < 504, (x - (i * 4 + (k + 3) % 4 + 1)) -/
lemma prod_eq_prod_of_mod_eq {x : ℝ} {k : ℕ} :
    ∏ i ∈ filter (fun i : Fin 2016 ↦ (↑i + 1) % 4 = k % 4) univ, (x - (↑i.val + 1)) = ∏ i ∈ range 504, (x - (i * 4 + ((k + 3) % 4 : ℕ) + 1)) := by
  have h_lt {i : ℕ} (hi : i ∈ range 504) : i * 4 + (k + 3) % 4 < 2016 := by
    apply lt_of_le_of_lt (b := 503 * 4 + 3)
    · gcongr
      · simp at hi
        exact Nat.le_of_lt_succ hi
      · apply Nat.le_of_lt_succ
        apply Nat.mod_lt
        simp
    · simp
  have : (range 504).attach.image (fun i => (⟨i.1 * 4 + (k + 3) % 4, by apply h_lt; exact i.2⟩ : Fin 2016)) = filter (fun i : Fin 2016 ↦ (↑i + 1) % 4 = k % 4) univ := by
    ext ⟨i, hi⟩
    simp
    constructor
    · intro h
      obtain ⟨a, ha, h⟩ := h
      rw [←h, Nat.add_mod, Nat.add_mod (a * 4)]
      simp [add_assoc]
    · intro h
      use i / 4
      constructor
      · exact Nat.div_lt_of_lt_mul hi
      · have : (k + 3) % 4 = i % 4 := by
          rw [Nat.add_mod, ←h, ←Nat.add_mod]
          simp [add_assoc]
        rw [this]
        exact Nat.div_add_mod' i 4
  rw [←this, prod_image, ←prod_attach (range 504)]
  · apply prod_congr rfl
    intro i hi
    simp [add_assoc]
  · intro x hx y hy h
    simp at h
    exact Subtype.eq h

/- We divide x ∈ ℝ into four cases :  i) x = 1.2....2016; ii) 4k+1< x < 2k+2 ∨ 4k+3 < x < 4k+4; iii) x < 1 ∨ x>2016 ∨ (4k < x < 4k + 1) iv) 4k + 2 < x < 4k + 3 -/
lemma cases_real {x : ℝ} : (∃ i ∈ Icc (1 : ℕ) 2016, x = ↑i) ∨ (∃ k ∈ range 504, x ∈ Set.Ioo (4 * ↑k + 1 : ℝ) (4 * ↑k + 2) ∪ Set.Ioo (4 * ↑k + 3 : ℝ) (4 * ↑k + 4)) ∨
    (x < 1 ∨ x > 2016 ∨ (∃ k ∈ range 504, x ∈ Set.Ioo (4 * k : ℝ) (4 * k + 1))) ∨ ∃ k ∈ range 504, x ∈ Set.Ioo (4 * k + 2 : ℝ) (4 * k + 3) := by
  by_cases h₁ : x < 1
  · simp [h₁]
  by_cases h₂ : x > 2016
  · simp [h₂]
  · -- wlog, assume 1 ≤ x ≤ 2016
    -- Consider r = ⌊x⌋
    let r := ⌊x⌋₊
    have hr : r ∈ Icc 1 2016 := by
      simp [r]
      constructor
      · simp at h₁
        exact h₁
      · simp at h₂
        exact Nat.floor_le_of_le h₂
    by_cases h₃ : x = r
    · left
      use r
    · -- If x ≠ r, we know that r < x < r + 1.
      -- It is easy to represent r as 4k + m for some k and m ∈ {0, 1, 2, 3}.
      right
      have hr' : r ≠ 2016 := by
        by_contra h
        simp at h₂
        apply h₃
        rw [h]
        apply le_antisymm h₂
        by_contra h'
        simp at h'
        have  : r < 2016 := by
          simp [r]
          apply Nat.floor_lt ?_ |>.mpr
          · exact h'
          · simp at h₁
            apply le_trans ?_ h₁
            simp
        simp [h] at this
      let k := r / 4
      have hk : k < 504 := by
        have hr : r < 2016 := by
          simp at hr
          apply lt_of_le_of_ne hr.2 hr'
        simp [k]
        apply Nat.div_lt_iff_lt_mul ?_ |>.mpr
        simp [hr]
        simp
      have hr : r = 4 * k + (r % 4) := by
        exact Eq.symm (Nat.div_add_mod r 4)
      have hl : r < x := by
        apply lt_of_le_of_ne
        · simp [r]
          simp at h₁
          have : x ≥ 0 := by apply le_trans ?_ h₁; simp
          exact Nat.floor_le this
        · exact fun a ↦ h₃ (id (Eq.symm a))
      have hg : x < r + 1 := by
        simp [r]
        exact Nat.lt_floor_add_one x
      rw [hr] at hl hg
      -- By analysis on mod 4, we can divide the cases into four cases.
      mod_cases hm : r % 4
      · have hm : r % 4 = 0 := by exact hm
        simp [hm] at hl hg
        right; left; right; right
        simp
        use k
      · have hm : r % 4 = 1 := by exact hm
        simp [hm, add_assoc] at hl hg
        norm_num at hg
        left
        simp
        use k, hk
        left
        use hl
      · have hm : r % 4 = 2 := by exact hm
        simp [hm, add_assoc] at hl hg
        norm_num at hg
        right; right
        simp
        use k
      · have hm : r % 4 = 3 := by exact hm
        simp [hm, add_assoc] at hl hg
        norm_num at hg
        left
        simp
        use k, hk
        right
        exact ⟨hl, hg⟩


/- If x ∈ 1 .... 2016, then the equation does not hold. -/
lemma ne_of_mem_Icc {x : ℝ} (hx : ∃ i ∈ Icc (1 : ℕ) 2016, x = ↑i) : ¬∏ i ∈ range 504, (x - (↑i * 4 + 1)) * (x - (↑i * 4 + 4)) = ∏ i ∈ range 504, (x - (↑i * 4 + 2)) * (x - (↑i * 4 + 3)) := by
  obtain ⟨i, hi, heq⟩ := hx
  simp at hi
  obtain ⟨h₁, h₂⟩ := hi
  -- prove by case analysis on i % 4
  mod_cases h : i % 4
  · -- If i % 4 = 0, then the LHS is zero while the RHS is non-zero.
    have h : i % 4 = 0 := by exact h
    have hi : 1 ≤ i / 4 := by
      by_contra h'
      simp at h'
      interval_cases i
      all_goals norm_num at h
    have : ∏ i ∈ range 504, (x - (↑i * 4 + 1)) * (x - (↑i * 4 + 4)) = 0 := by
      apply prod_eq_zero (i := i / 4 - 1)
      · simp
        apply Nat.sub_lt_left_of_lt_add
        · exact hi
        · simp
          apply Nat.lt_of_le_pred
          · simp
          · simp
            exact Nat.div_le_of_le_mul h₂
      · simp
        right
        rw [heq, Nat.cast_sub hi, Nat.cast_div]
        ring_nf
        · exact Nat.dvd_of_mod_eq_zero h
        · simp
    rw [this]
    by_contra h'
    rw [eq_comm] at h'
    apply prod_eq_zero_iff.mp at h'
    obtain ⟨j, hj, heq⟩ := h'
    simp at heq
    rcases heq with h₁ | h₂
    · apply sub_eq_zero.mp at h₁
      rw [h₁] at heq
      norm_cast at heq
      rw [←heq] at h
      simp [Nat.add_mod] at h
    · apply sub_eq_zero.mp at h₂
      rw [h₂] at heq
      norm_cast at heq
      rw [←heq] at h
      simp [Nat.add_mod] at h
  · -- All other cases follow the same pattern.
    have h : i % 4 = 1 := by exact h
    have : ∏ i ∈ range 504, (x - (↑i * 4 + 1)) * (x - (↑i * 4 + 4)) = 0 := by
      apply prod_eq_zero (i := i / 4)
      · simp
        by_contra h'
        simp at h'
        apply Nat.le_div_iff_mul_le (by simp) |>.mp at h'
        interval_cases i
        simp at h
      · simp
        left
        rw [heq]
        apply sub_eq_zero.mpr
        norm_cast
        rw [←h]
        exact Eq.symm (Nat.div_add_mod' i 4)
    rw [this]
    by_contra h'
    rw [eq_comm] at h'
    apply prod_eq_zero_iff.mp at h'
    obtain ⟨j, hj, heq⟩ := h'
    simp at heq
    rcases heq with h₁ | h₂
    · apply sub_eq_zero.mp at h₁
      rw [h₁] at heq
      norm_cast at heq
      rw [←heq] at h
      simp [Nat.add_mod] at h
    · apply sub_eq_zero.mp at h₂
      rw [h₂] at heq
      norm_cast at heq
      rw [←heq] at h
      simp [Nat.add_mod] at h
  · have h : i % 4 = 2 := by exact h
    have : ∏ i ∈ range 504, (x - (↑i * 4 + 2)) * (x - (↑i * 4 + 3)) = 0 := by
      apply prod_eq_zero (i := i / 4)
      · simp
        by_contra h'
        simp at h'
        apply Nat.le_div_iff_mul_le (by simp) |>.mp at h'
        interval_cases i
        simp at h
      · simp
        left
        rw [heq]
        apply sub_eq_zero.mpr
        norm_cast
        rw [←h]
        exact Eq.symm (Nat.div_add_mod' i 4)
    rw [this]
    by_contra h'
    apply prod_eq_zero_iff.mp at h'
    obtain ⟨j, hj, heq⟩ := h'
    simp at heq
    rcases heq with h₁ | h₂
    · apply sub_eq_zero.mp at h₁
      rw [h₁] at heq
      norm_cast at heq
      rw [←heq] at h
      simp [Nat.add_mod] at h
    · apply sub_eq_zero.mp at h₂
      rw [h₂] at heq
      norm_cast at heq
      rw [←heq] at h
      simp [Nat.add_mod] at h
  · have h : i % 4 = 3 := by exact h
    have : ∏ i ∈ range 504, (x - (↑i * 4 + 2)) * (x - (↑i * 4 + 3)) = 0 := by
      apply prod_eq_zero (i := i / 4)
      · simp
        by_contra h'
        simp at h'
        apply Nat.le_div_iff_mul_le (by simp) |>.mp at h'
        interval_cases i
        simp at h
      · simp
        right
        rw [heq]
        apply sub_eq_zero.mpr
        norm_cast
        rw [←h]
        exact Eq.symm (Nat.div_add_mod' i 4)
    rw [this]
    by_contra h'
    apply prod_eq_zero_iff.mp at h'
    obtain ⟨j, hj, heq⟩ := h'
    simp at heq
    rcases heq with h₁ | h₂
    · apply sub_eq_zero.mp at h₁
      rw [h₁] at heq
      norm_cast at heq
      rw [←heq] at h
      simp [Nat.add_mod] at h
    · apply sub_eq_zero.mp at h₂
      rw [h₂] at heq
      norm_cast at heq
      rw [←heq] at h
      simp [Nat.add_mod] at h

/- If ∃ k, 4k+ 1 < x < 4k + 2 ∨ 4k+3 < x < 4k+4, then the equation does not hold. -/
lemma ne_of_mem_Ioo_1_2_or_Ioo_3_4 {x : ℝ} (hx : ∃ k ∈ range 504, x ∈ Set.Ioo (4 * ↑k + 1 : ℝ) (4 * ↑k + 2) ∪ Set.Ioo (4 * ↑k + 3 : ℝ) (4 * ↑k + 4)) :
    ¬∏ i ∈ range 504, (x - (↑i * 4 + 1)) * (x - (↑i * 4 + 4)) = ∏ i ∈ range 504, (x - (↑i * 4 + 2)) * (x - (↑i * 4 + 3)) := by
  obtain ⟨k, hk, h⟩ := hx
  simp at h
  have hlt : 4 * k + 1 < x := by
    rcases h with h | h
    · exact h.1
    · apply lt_trans ?_ h.1
      simp
  have hgt : x < 4 * k + 4 := by
    rcases h with h | h
    · apply lt_trans h.2
      simp
      norm_num
    · exact h.2
  have hrange : range 504 = (range 504).erase k ∪ {k} := by
    rw [union_comm, union_erase_of_mem]
    · rw [eq_comm]
      apply union_eq_right.mpr
      simp at hk ⊢
      exact hk
    · simp
  have hdis : Disjoint ((range 504).erase k) {k} := by simp
  -- We first show that the product of the left-hand side is negative.
  have hLHS : ∏ i ∈ range 504, (x - (↑i * 4 + 1)) * (x - (↑i * 4 + 4)) < 0 := by
    rw [hrange, prod_union hdis]
    simp
    apply mul_neg_of_pos_of_neg
    · apply prod_pos
      intro i hi
      simp at hi
      obtain ⟨h₁, h₂⟩ := hi
      -- For $j=0,1, \ldots, 503$ with $j \neq k$, the product $(x-4 j-1)(x-4 j-4)$ is positive
      rcases lt_or_gt_of_ne h₁ with h₁ | h₁
      · apply mul_pos
        · simp
          apply lt_trans ?_ hlt
          rw [mul_comm]
          gcongr
        · simp
          apply lt_trans ?_ hlt
          apply lt_of_le_of_lt (b := (k - 1 : ℕ) * 4 + (4 : ℝ))
          · gcongr
            exact Nat.le_sub_one_of_lt h₁
          · rw [Nat.cast_sub (by exact Nat.one_le_of_lt h₁)]
            apply sub_pos.mp
            ring_nf
            simp
      · apply mul_pos_of_neg_of_neg
        · simp
          apply lt_trans hgt
          apply lt_of_lt_of_le (b := (k + 1 : ℕ) * 4 + (1 : ℝ))
          · simp
            apply sub_pos.mp
            ring_nf
            simp
          · gcongr
            exact h₁
        · simp
          apply lt_trans hgt
          rw [mul_comm]
          gcongr
    · -- For $j=k$, the product $(x-4 k-1)(x-4 k-4)$ is negative.
      apply mul_neg_of_pos_of_neg
      · simp
        rw [mul_comm]
        exact hlt
      · simp
        rw [mul_comm]
        exact hgt
  -- On the other hand, each product $(x-4 j-2)(x-4 j-3)$ on the right-hand side of (1) is positive.
  have hRHS : ∏ i ∈ range 504, (x - (↑i * 4 + 2)) * (x - (↑i * 4 + 3)) > 0 := by
    apply prod_pos
    intro i hi
    by_cases hi : i = k
    · simp [hi]
      rcases h with h | h
      · apply mul_pos_of_neg_of_neg
        · simp
          rw [mul_comm]
          exact h.2
        · simp
          apply lt_trans h.2
          apply sub_pos.mp
          ring_nf
          simp
      · apply mul_pos
        · simp
          apply lt_trans ?_ h.1
          apply sub_pos.mp
          ring_nf
          simp
        · simp
          rw [mul_comm]
          exact h.1
    · rcases lt_or_gt_of_ne hi with hi | hi
      · apply mul_pos
        · simp
          apply lt_trans ?_ hlt
          apply lt_of_le_of_lt (b := (k - 1 : ℕ) * 4 + (2 : ℝ))
          · gcongr
            exact Nat.le_sub_one_of_lt hi
          · apply sub_pos.mp
            rw [Nat.cast_sub (by exact Nat.one_le_of_lt hi)]
            ring_nf
            simp
        · simp
          apply lt_trans ?_ hlt
          apply lt_of_le_of_lt (b := (k - 1 : ℕ) * 4 + (3 : ℝ))
          · gcongr
            exact Nat.le_sub_one_of_lt hi
          · apply sub_pos.mp
            rw [Nat.cast_sub (by exact Nat.one_le_of_lt hi)]
            ring_nf
            simp
      · apply mul_pos_of_neg_of_neg
        · simp
          apply lt_trans hgt
          apply lt_of_lt_of_le (b := (k + 1 : ℕ) * 4 + (2 : ℝ))
          · simp
            apply sub_pos.mp
            ring_nf
            simp
          · gcongr
            exact hi
        · simp
          apply lt_trans hgt
          apply lt_of_lt_of_le (b := (k + 1 : ℕ) * 4 + (3 : ℝ))
          · simp
            apply sub_pos.mp
            ring_nf
            simp
          · gcongr
            exact hi
  apply ne_of_lt
  -- LHS < 0 < RHS
  apply lt_trans hLHS hRHS


/- If x < 1 ∨ x > 2016 or x ∈ (4k, 4k+1) for some k, then the equation does not hold. -/
lemma ne_of_lt_one_or_gt_2016_or_mem_Ioo_0_1 {x : ℝ} (hx : x < 1 ∨ x > 2016 ∨ ∃ k ∈ range 504, x ∈ Set.Ioo (4 * ↑k : ℝ) (4 * ↑k + 1)) :
    ¬∏ i ∈ range 504, (x - (↑i * 4 + 1)) * (x - (↑i * 4 + 4)) = ∏ i ∈ range 504, (x - (↑i * 4 + 2)) * (x - (↑i * 4 + 3)) := by
  -- We prove that LHS < RHS
  apply ne_of_lt
  apply prod_lt_prod
  · -- By case analysis on x, it is easy to show that all factors are positive
    rcases hx with hx | hx | hx
    · intro i hi
      apply mul_pos_of_neg_of_neg
      · simp
        apply lt_of_lt_of_le hx
        simp
      · simp
        apply lt_trans hx
        apply sub_pos.mp
        ring_nf
        norm_cast
        simp
    · intro i hi
      apply mul_pos
      · simp
        apply lt_trans ?_ hx
        apply sub_pos.mp
        ring_nf
        simp at hi ⊢
        apply lt_of_le_of_lt (b := 503 * 4)
        · gcongr
          norm_cast
          exact Nat.le_of_lt_succ hi
        · norm_num
      · simp
        apply lt_of_le_of_lt ?_ hx
        apply sub_nonneg.mp
        ring_nf
        simp at hi ⊢
        apply le_trans (b := 503 * 4)
        · gcongr
          norm_cast
          exact Nat.le_of_lt_succ hi
        · norm_num
    · obtain ⟨k, hk, heq⟩ := hx
      simp at heq
      intro i _
      by_cases hik : i < k
      · apply mul_pos
        · simp
          apply lt_of_le_of_lt ?_ heq.1
          trans (k - 1 : ℕ) * 4 + 1
          · gcongr
            exact Nat.le_sub_one_of_lt hik
          · apply sub_nonneg.mp
            rw [Nat.cast_sub (by exact Nat.one_le_of_lt hik)]
            ring_nf
            simp
        · simp
          apply lt_of_le_of_lt ?_ heq.1
          trans (k - 1 : ℕ) * 4 + 4
          · gcongr
            exact Nat.le_sub_one_of_lt hik
          · apply sub_nonneg.mp
            rw [Nat.cast_sub (by exact Nat.one_le_of_lt hik)]
            ring_nf
            simp
      · simp at hik
        apply mul_pos_of_neg_of_neg
        · simp
          apply lt_of_lt_of_le heq.2
          trans 4 * i + 1
          · gcongr
          · apply sub_nonneg.mp
            ring_nf
            simp
        · simp
          apply lt_of_lt_of_le heq.2
          trans 4 * i + 1
          · gcongr
          · apply sub_nonneg.mp
            ring_nf
            simp
  · -- Then for any i < 504, we have (x - (↑i * 4 + 1)) * (x - (↑i * 4 + 4)) < (x - (↑i * 4 + 2)) * (x - (↑i * 4 + 3)), which is equivalent to 0 < 2.
    intro i hi
    apply sub_nonneg.mp
    ring_nf
    simp
  · use 0
    simp
    apply sub_pos.mp
    ring_nf
    simp

/- If 4k+2 < x < 4k + 3, we prove that LHS < RHS -/
lemma ne_of_mem_Ioo_2_3 {x : ℝ} (hx : ∃ k ∈ range 504, x ∈ Set.Ioo (4 * ↑k + 2 : ℝ) (4 * ↑k + 3)) :
    ¬∏ i ∈ range 504, (x - (↑i * 4 + 1)) * (x - (↑i * 4 + 4)) = ∏ i ∈ range 504, (x - (↑i * 4 + 2)) * (x - (↑i * 4 + 3)) := by
  -- We need to rearrange the product as
  -- (x - 1) * (x - (503 * 4 + 4)) * ∏ x_1 ∈ range 503, (x - ((↑x_1 + 1) * 4 + 1)) * (x - (↑x_1 * 4 + 4)) <
  -- (x - 2) * (x - (503 * 4 + 3)) * ∏ x_1 ∈ range 503, (x - ((↑x_1 + 1) * 4 + 2)) * (x - (↑x_1 * 4 + 3))
  have rearrange {f g : ℕ → ℝ} {x : ℝ} : ∏ i ∈ range 504, (x - f i) * (x - g i) = (x - f 0) * (x - g 503) * ∏ i ∈ range 503, (x - f (i + 1)) * (x - g i) := by
    rw [prod_mul_distrib, prod_mul_distrib]
    rw [prod_range_succ', prod_range_succ _ 503]
    ring
  obtain ⟨k, hk, h⟩ := hx
  simp at hk h
  -- All factors in the product are positive.
  have hpos : ∀ i ∈ range 503, 0 < (x - ((↑i + 1) * 4 + 2)) * (x - (↑i * 4 + 3)) := by
    intro i hi
    by_cases hi : i < k
    · apply mul_pos
      · simp
        apply lt_of_le_of_lt ?_ h.1
        rw [mul_comm]
        gcongr
        norm_cast
      · simp
        apply lt_of_le_of_lt ?_ h.1
        trans (k - 1 : ℕ) * 4 + 3
        · gcongr
          exact Nat.le_sub_one_of_lt hi
        · apply sub_nonneg.mp
          rw [Nat.cast_sub (by exact Nat.one_le_of_lt hi)]
          ring_nf
          simp
    · simp at hi
      apply mul_pos_of_neg_of_neg
      · simp
        apply lt_of_lt_of_le h.2
        trans 4 * i + 3
        · gcongr
        · apply sub_nonneg.mp
          ring_nf
          simp
      · simp
        apply lt_of_lt_of_le h.2
        rw [mul_comm]
        gcongr
  rw [rearrange, rearrange]
  simp
  apply ne_of_lt
  -- However, note that (x - 2016) and (x - 2015) are negative.
  -- Therefore, we need to prove that -(x - 1) * (x - 2016) > -(x - 2) * (x - 2015) and
  -- ∏ x_1 ∈ range 503, (x - ((↑x_1 + 1) * 4 + 1)) * (x - (↑x_1 * 4 + 4)) > ∏ x_1 ∈ range 503, (x - ((↑x_1 + 1) * 4 + 2)) * (x - (↑x_1 * 4 + 3))
  apply lt_of_neg_lt_neg
  rw [←neg_mul, ←neg_mul, ←neg_mul, ←neg_mul]
  apply mul_lt_mul
  · -- The first inequality is trivial.
    apply sub_pos.mp
    ring_nf
    simp
  · -- As for the second inequality, we need to prove that (x - ((↑x_1 + 1) * 4 + 1)) * (x - (↑x_1 * 4 + 4)) >  (x - ((↑x_1 + 1) * 4 + 2)) * (x - (↑x_1 * 4 + 3)),
    -- which is equivalent to 0 < 2.
    apply prod_le_prod
    · exact fun i hi ↦ le_of_lt (hpos i hi)
    · intro i hi
      apply sub_nonneg.mp
      ring_nf
      simp
  · apply prod_pos hpos
  · simp
    apply mul_nonneg_of_nonpos_of_nonpos
    · simp
      apply le_of_lt
      apply lt_trans ?_ h.1
      apply sub_pos.mp
      ring_nf
      norm_cast
      simp
    · simp
      norm_num
      apply le_of_lt
      apply lt_trans h.2
      apply lt_of_le_of_lt (b := 4 * 503 + 3)
      · gcongr
        norm_cast
        exact Nat.le_of_lt_succ hk
      · norm_num

/- The equation  $$ (x-1)(x-2) \cdots(x-2016)=(x-1)(x-2) \cdots(x-2016) $$  is written on the board.
One tries to erase some linear factors from both sides so that each side still has at least one factor,
and the resulting equation has no real roots. Find the least number of linear factors one needs to erase to achieve this. Answer. 2016. -/
theorem algebra_24860 {f : Fin 2016 → ℕ} (hf : ∀ i, f i = i.val + 1) :
    IsLeast {n : ℕ | ∃ elim_left ⊆ univ, ∃ elim_right ⊆ univ, elim_left.card + elim_right.card = n ∧
      ¬∃ x : ℝ, ∏ i ∈ univ \ elim_left, (x - f i) = ∏ i ∈ univ \ elim_right, (x - f i)} 2016 := by
  constructor
  · simp
    -- If n = 2016, we show that there exists a way to erase 2016 factors such that the resulting equation has no real roots.
    -- For the left-hand side, we ease x - k with k ≡ 2, 3 (mod 4).
    let elim_left := univ.filter (fun i : Fin 2016 => (i.val + 1) % 4 = 2) ∪ univ.filter (fun i : Fin 2016 => (i.val + 1) % 4 = 3)
    have hcard_left : elim_left.card = 1008 := by
      rw [card_union_of_disjoint, show 2 = 2 % 4 by simp, show 3 = 3 % 4 by simp]
      rw [card_filter_mod_eq, card_filter_mod_eq]
      apply disjoint_left.mpr
      intro i hi
      simp at hi ⊢
      simp [hi]
    -- For the right-hand side, we ease x - k with k ≡ 0, 1 (mod 4).
    let elim_right := univ.filter (fun i : Fin 2016 => (i.val + 1) % 4 = 0) ∪ univ.filter (fun i : Fin 2016 => (i.val + 1) % 4 = 1)
    have hcard_right : elim_right.card = 1008 := by
      rw [card_union_of_disjoint, show 0 = 0 % 4 by simp, show 1 = 1 % 4 by simp]
      rw [card_filter_mod_eq, card_filter_mod_eq]
      apply disjoint_left.mpr
      intro i hi
      simp at hi ⊢
      simp [hi]
    have hsdiff : univ \ elim_left = elim_right := by
      ext i
      simp [elim_left, elim_right]
      mod_cases h : (i.val + 1) % 4
      · have h : (i.val + 1) % 4 = 0 := by exact h
        simp [h]
      · have h : (i.val + 1) % 4 = 1 := by exact h
        simp [h]
      · have h : (i.val + 1) % 4 = 2 := by exact h
        simp [h]
      · have h : (i.val + 1) % 4 = 3 := by exact h
        simp [h]
    have hsdiff' : univ \ elim_right = elim_left := by
      rw [←hsdiff]
      simp
    use elim_left, elim_right
    simp [hcard_left, hcard_right]
    -- Therefore, it suffices to show that no real number $x$ satisfies the equation.
    intro x
    rw [hsdiff, hsdiff']
    -- Simplify the equation.
    have hLHS : ∏ i ∈ elim_right, (x - ↑(f i)) = ∏ i ∈ range 504, (x - (i * 4 + 1)) * (x - (i * 4 + 4)) := by
      unfold elim_right
      rw [prod_union, mul_comm, prod_mul_distrib]
      · obtain h₁ := prod_eq_prod_of_mod_eq (x := x) (k := 1)
        obtain h₂ := prod_eq_prod_of_mod_eq (x := x) (k := 0)
        simp at h₁ h₂
        simp [hf]
        rw [h₁, h₂]
        simp [add_assoc]
        left
        norm_num
      · apply disjoint_left.mpr
        intro i hi
        simp at hi ⊢
        simp [hi]
    have hRHS : ∏ i ∈ elim_left, (x - ↑(f i)) = ∏ i ∈ range 504, (x - (i * 4 + 2)) * (x - (i * 4 + 3)) := by
      unfold elim_left
      rw [prod_union, mul_comm, prod_mul_distrib]
      · obtain h₁ := prod_eq_prod_of_mod_eq (x := x) (k := 2)
        obtain h₂ := prod_eq_prod_of_mod_eq (x := x) (k := 3)
        simp at h₁ h₂
        simp [hf]
        rw [h₁, h₂, mul_comm]
        simp [add_assoc]
        norm_num
      · apply disjoint_left.mpr
        intro i hi
        simp at hi ⊢
        simp [hi]
    rw [hLHS, hRHS]
    rcases cases_real (x := x) with hx | hx | hx | hx
    · -- Cases 1. x = 1.2...2016
      apply ne_of_mem_Icc hx
    · -- Cases 2. x ∈ (4k + 1, 4k + 2) or (4k + 3, 4k + 4) for some k.
      apply ne_of_mem_Ioo_1_2_or_Ioo_3_4 hx
    · -- Cases 3. x < 1 or x > 2016 or (4k, 4k + 1) for some k.
      apply ne_of_lt_one_or_gt_2016_or_mem_Ioo_0_1 hx
    · -- Cases 4. x ∈ (4k + 2, 4k + 3) for some k.
      apply ne_of_mem_Ioo_2_3 hx
  · -- Since there are 2016 common linear factors on both sides, we need to erase at least 2016 factors.
    intro n hn
    simp at hn
    obtain ⟨elim_left, elim_right, hcard, hno_real_root⟩ := hn
    by_contra h
    simp at h
    rw [←hcard] at h
    -- Otherwise, by our leema, there exists a common factor which is not eliminated.
    obtain ⟨i, hi⟩ := sdiff_non_empty_of_card_add_card_le_2016 h
    simp at hi
    -- Therefore, i.val + 1 is a real root of the equation.
    obtain hno_real_root_i := hno_real_root (f i)
    apply hno_real_root_i
    -- Since the both sides of the equation equal to zero.
    trans 0
    · apply prod_eq_zero (i := i)
      · simp [hi.1]
      · simp
    · symm
      apply prod_eq_zero (i := i)
      · simp [hi.2]
      · simp
