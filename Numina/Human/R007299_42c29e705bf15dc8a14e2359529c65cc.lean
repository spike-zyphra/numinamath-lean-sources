import Mathlib
set_option maxHeartbeats 500000

/- Prove that there do not exist pairwise distinct complex numbers $a, b, c$, and $d$ such that

$$
a^{3}-b c d=b^{3}-c d a=c^{3}-d a b=d^{3}-a b c .
$$-/
theorem algebra_610613 : ¬∃ a b c d : ℂ, a ^ 3 - b * c * d = b ^ 3 - c * d * a ∧ b ^ 3 - c * d * a = c ^ 3 - d * a * b ∧ c ^ 3 - d * a * b = d ^ 3 - a * b * c ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  -- Assume on the contrary that such 4 distinct complex numbers exist.
  by_contra!
  obtain ⟨a, b, c, d, h₀, h₁, h₂, g₀, g₁, g₂, g₃, g₄, g₅⟩ := this
  -- Prove a lemma that it is impossible for non-zero complex numbers (not all zero) x, y, z with x³ = y³ = z³ = -xyz.
  have lm (x y z : ℂ) (g₀ : x ≠ y) (g₁ : y ≠ z) (g₂ : z ≠ x) (g₃ : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (h₀ : x ^ 3 = y ^ 3) (h₁ : y ^ 3 = z ^ 3) (h₂ : z ^ 3 = -(x * y * z)) : False := by
    -- Let q = x ^ 3.
    let q := x ^ 3
    -- Now x, y, z are distinct roots of the polynomial P = X³ - q = 0.
    let P : Polynomial ℂ := .X ^ 3 - .C q
    -- Show that leading coefficient of P is 1.
    have h₃ : P.leadingCoeff = 1 := by
      simp [P]
    -- First show that P is monic.
    have h₄ : P.Monic := by
      simp [Polynomial.Monic, h₃]
    -- Show that P ≠ 0.
    have h₅ : P ≠ 0 := by
      simp [<-Polynomial.leadingCoeff_ne_zero, h₄]
    -- Show that {x, y, z} ≤ P.roots.
    have h₆ : {x, y, z} ≤ P.roots := by
      simp
      iterate 2 rw [Multiset.cons_le_of_not_mem (by simp; tauto)]
      rw [Multiset.singleton_le]
      -- It suffices to show that x, y, z ∈ P.roots.
      simp [Polynomial.mem_roots, h₅, P]
      simp [q, h₀, h₁]
    -- Show that P.natDegree = 3.
    have h₇ : P.natDegree = 3 := by
      simp [P]
    -- Show that P.roots.card ≥ 3.
    have h₈ : P.roots.card ≥ 3 := by
      rw [show 3 = ({x, y, z} : Multiset ℂ).card by simp]
      apply Multiset.card_le_card h₆
    -- Show that P.roots.card = 3.
    replace h₈ := (le_antisymm_iff.mpr ⟨Polynomial.card_roots' P, h₇ ▸ h₈⟩).trans h₇
    -- Show that P = {x, y, z} by showing that P.roots has no duplications.
    have h₉ : P.roots.Nodup := by
      rw [<-Multiset.dedup_card_eq_card_iff_nodup]
      apply le_antisymm
      . apply Multiset.card_le_card
        apply Multiset.dedup_le
      . rw [<-Multiset.Nodup.le_dedup_iff_le] at h₆
        apply Multiset.card_le_card at h₆
        simp [<-h₈] at h₆
        exact h₆
        simp
        tauto
    replace h₆ : P.roots = {x, y, z} := by
      have : ({x, y, z} : Multiset ℂ).Nodup := by
        simp
        tauto
      apply Multiset.Nodup.toFinset_inj h₉ (by simp; tauto)
      symm
      apply Finset.eq_of_subset_of_card_le
      rw [Multiset.toFinset_subset, <-Multiset.le_iff_subset this]
      exact h₆
      rw [Multiset.toFinset_card_of_nodup h₉, Multiset.toFinset_card_of_nodup this, h₈]
      simp
    -- Factorize P.
    have h₁₀ := @Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq _ _ _ P h₄ (h₈ ▸ h₇.symm)
    simp [h₆] at h₁₀
    -- Now evaluate both sides at X = 0 to get that q = xyz.
    have h₁₁ : q = x * y * z := by
      replace h₁₀ := congr_arg (Polynomial.eval 0 ·) h₁₀
      simp [P] at h₁₀
      linear_combination -h₁₀
    -- Now we have -xyz = q = 0, which is a contradiction.
    simp [q] at h₁₁
    replace h₁₁ := h₁₁.symm ▸ h₀ ▸ h₁ ▸ h₂
    rw [<-add_eq_zero_iff_eq_neg] at h₁₁
    ring_nf at h₁₁
    simp at h₁₁
    simp [h₁₁] at h₀ h₂
    symm at h₀
    simp at h₀
    tauto
  by_cases hzero : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0
  . -- Suppose one of them is equal to zero.
    have h₀' := h₀.trans h₁
    have h₁' := h₁.trans h₂
    have h₂' := h₀'.trans h₂
    rcases hzero with (h₃ | h₃ | h₃ | h₃)
    <;> simp [h₃] at h₀ h₁ h₂ h₀' h₁' h₂'
    . subst a
      apply lm b c d
      all_goals
        tauto
    . subst b
      apply lm c d a
      all_goals
        try tauto
    . subst c
      apply lm d a b
      all_goals
        try tauto
    . subst d
      apply lm a b c
      all_goals
        try tauto
  . -- Suppose all of them are non-zero.
    -- Let q = abcd and k = a ^ 3 - bcd.
    let q := a * b * c * d
    let k := a ^ 3 - b * c * d
    -- Show that x ^ 4 - k * x - q = 0 is satisfied by a, b, c and d.
    have h₃ {x : ℂ} : x ∈ ({a, b, c, d} : Set ℂ) → x ^ 4 - k * x - q = 0 := by
      intro h₄
      simp at h₄
      rcases h₄ with (h₄ | h₄ | h₄ | h₄) <;> simp [h₄, k, q]
      . ring
      . rw [h₀]
        ring
      . rw [h₀, h₁]
        ring
      . rw [h₀, h₁, h₂]
        ring
    -- Since they are distinct roots of x ^ 4 - kx - q = 0, we can apply Vieta's formula to show that abcd = q.
    -- Let P be the polynomial x⁴ - kx - q.
    let P : Polynomial ℂ := .X ^ 4 - .C k * .X - .C q
    -- Show that leading coefficient of P is 1.
    have h₄ : P.leadingCoeff = 1 := by
      simp [P]
      iterate 2 rw [Polynomial.leadingCoeff_sub_of_degree_lt]
      . rw [Polynomial.leadingCoeff_X_pow]
      . simp [Polynomial.degree_X_pow]
        calc
          _ < 1 + 1 := by
            apply WithBot.add_lt_add_right (by simp)
            apply Polynomial.degree_C_lt
          _ < (4 : WithBot ℕ) := by
            norm_num
      . rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_X_pow]
        calc
          _ < 1 := by
            apply Polynomial.degree_C_lt
          _ < (4 : WithBot ℕ) := by
            norm_num
        simp [Polynomial.degree_X_pow]
        calc
          _ < 1 + 1 := by
            apply WithBot.add_lt_add_right (by simp)
            apply Polynomial.degree_C_lt
          _ < (4 : WithBot ℕ) := by
            norm_num
    -- First show that P is monic.
    have h₅ : P.Monic := by
      simp [Polynomial.Monic, h₄]
    -- Show that P ≠ 0.
    have h₆ : P ≠ 0 := by
      simp [<-Polynomial.leadingCoeff_ne_zero, h₄]
    -- Show that {a, b, c, d} ≤ P.roots.
    have h₇ : {a, b, c, d} ≤ P.roots := by
      simp
      iterate 3 rw [Multiset.cons_le_of_not_mem (by simp; tauto)]
      rw [Multiset.singleton_le]
      -- It suffices to show that a, b, c, d ∈ P.roots.
      simp at h₃
      simp [Polynomial.mem_roots, h₆, P, h₃]
    -- Show that P.natDegree = 4.
    have h₈ : P.natDegree = 4 := by
      simp [P]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
      by_cases hk : k = 0
      . simp [hk]
      . rw [Polynomial.natDegree_mul, Polynomial.natDegree_X_pow, Polynomial.natDegree_X, Polynomial.natDegree_C]
        norm_num
        simp [hk]
        simp
    -- Show that P.roots.card ≥ 4.
    have h₉ : P.roots.card ≥ 4 := by
      rw [show 4 = ({a, b, c, d} : Multiset ℂ).card by simp]
      apply Multiset.card_le_card h₇
    -- Show that P.roots.card = 4.
    replace h₉ := (le_antisymm_iff.mpr ⟨Polynomial.card_roots' P, h₈ ▸ h₉⟩).trans h₈
    -- Show that P = {a, b, c, d} by showing that P.roots has no duplications.
    have h₁₀ : P.roots.Nodup := by
      rw [<-Multiset.dedup_card_eq_card_iff_nodup]
      apply le_antisymm
      . apply Multiset.card_le_card
        apply Multiset.dedup_le
      . rw [<-Multiset.Nodup.le_dedup_iff_le] at h₇
        apply Multiset.card_le_card at h₇
        simp [<-h₉] at h₇
        exact h₇
        simp
        tauto
    replace h₇ : P.roots = {a, b, c, d} := by
      have : ({a, b, c, d} : Multiset ℂ).Nodup := by
        simp
        tauto
      apply Multiset.Nodup.toFinset_inj h₁₀ (by simp; tauto)
      symm
      apply Finset.eq_of_subset_of_card_le
      rw [Multiset.toFinset_subset, <-Multiset.le_iff_subset this]
      exact h₇
      rw [Multiset.toFinset_card_of_nodup h₁₀, Multiset.toFinset_card_of_nodup this, h₉]
      simp
    -- Factorize P.
    have h₁₁ := @Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq _ _ _ P h₅ (h₉ ▸ h₈.symm)
    simp [h₇] at h₁₁
    -- Now evaluate both sides at X = 0 to get that -q = abcd.
    have h₁₂ : -q = a * b * c * d := by
      replace h₁₁ := congr_arg (Polynomial.eval 0 ·) h₁₁
      simp [P] at h₁₁
      linear_combination -h₁₁
    -- Now we have abcd = q = 0, which is a contradiction.
    simp [q] at h₁₂
    rw [<-add_eq_zero_iff_neg_eq] at h₁₂
    ring_nf at h₁₂
    simp at h₁₂
    tauto
