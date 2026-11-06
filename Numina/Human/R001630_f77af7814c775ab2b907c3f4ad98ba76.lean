import Mathlib

open Real Finset

/- ∑ i < j, x i * x j * (x i ^ 2 + x j ^ 2) ≤ (∑ i, x i ^ 2) *∑ i < j, x i * x j -/
lemma inequalities_1 {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∑ i, ∑ j in Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) ≤ (∑ i, ∑ j in Ioi i, x i * x j) * ∑ i, x i ^ 2 := by

  trans ∑ i, ∑ j in Ioi i, x i * x j * ∑ i, x i ^ 2
  · apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left
    trans ∑ i ∈ {i, j}, x i ^ 2
    · rw [sum_insert]
      simp
      simp at hj ⊢
      exact Fin.ne_of_lt hj
    · apply sum_le_sum_of_subset_of_nonneg
      · simp
      · intro _ _ _
        positivity
    · apply mul_nonneg <;> apply hx
  · apply le_of_eq
    rw [sum_mul]
    congr
    ext i
    rw [sum_mul]

/- ∑ i < j, x i * x j * (x i ^ 2 + x j ^ 2) = (∑ i, x i ^ 2) *∑ i < j, x i * x j holds if and only if ∀ i < j, x i * x j = 0 ∨ ∑ k ∉ {i, j} x k ^ 2 = 0
  i.e., ∃ i j, i ≠ j ∀ k, k ≠ i → k ≠ j → x k = 0 -/
lemma inequalities_1_holds_of {x : Fin n → ℝ} (hn : n ≥ 2) (hx : ∀ i, 0 ≤ x i) (h : ∑ i, ∑ j in Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) = (∑ i, ∑ j in Ioi i, x i * x j) * ∑ i, x i ^ 2) :
    ∃ i j, i ≠ j ∧ ∀ k, k ≠ i → k ≠ j → x k = 0 := by
  by_contra hne
  push_neg at hne
  have : (univ.filter (fun i => 0 < x i)).card > 1 := by
    by_contra h
    simp at h
    set m := (univ.filter (fun i => 0 < x i)).card with ←hm
    interval_cases m
    · apply card_eq_zero.mp at hm
      apply filter_eq_empty_iff.mp at hm
      obtain ⟨k, _, _, hk⟩ := hne ⟨0, by exact Nat.zero_lt_of_lt hn⟩ ⟨1, by exact hn⟩ (by simp)
      have : x k = 0 := by
        apply le_antisymm
        · simp at hm
          apply hm
        · apply hx
      contradiction
    · obtain ⟨a, ha⟩ := card_eq_one.mp hm
      have ⟨b, hb⟩ : (univ.erase a).Nonempty := by
        simp
        refine one_lt_card_iff_nontrivial.mp ?_
        simp
        exact hn
      simp at hb
      have ⟨k, hka, _, hk⟩ := hne a b (Ne.symm hb)
      have : x k = 0 := by
        have : k ∉ filter (fun i => 0 < x i) univ := by
          rw [ha]
          simp [hka]
        simp at this
        apply le_antisymm
        · apply this
        · apply hx
      contradiction
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp this
  simp at hi hj
  clear this
  wlog hij : i < j generalizing i j with H
  · simp at hij
    have hij : j < i := by
      apply lt_of_le_of_ne
      · exact hij
      · apply Ne.symm
        assumption
    exact H j i (Ne.symm (by assumption)) hj hi hij
  · obtain ⟨k, hki, hkj, hk⟩ := hne i j (by assumption)
    have : x i * x j * (x i ^ 2 + x j ^ 2) < x i * x j * ∑ i, x i ^ 2 := by
      apply mul_lt_mul_of_pos_left
      · apply lt_of_eq_of_lt (b := ∑ i ∈ {i, j}, x i ^ 2)
        · rw [sum_insert]
          · simp
          · simp
            assumption
        · apply sum_lt_sum_of_subset (i := k)
          · simp
          · simp
          · simp [hki, hkj]
          · apply sq_pos_of_ne_zero hk
          · intro _ _ _
            positivity
      · apply mul_pos <;> assumption
    have : ∑ i, ∑ j in Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) ≠ (∑ i, ∑ j in Ioi i, x i * x j) * ∑ i, x i ^ 2 := by
      apply ne_of_lt
      have : (∑ i : Fin n, ∑ j ∈ Ioi i, x i * x j) * ∑ i : Fin n, x i ^ 2 = ∑ i : Fin n, ∑ j ∈ Ioi i, x i * x j * ∑ i : Fin n, x i ^ 2 := by
        rw [sum_mul]
        congr
        ext i
        rw [sum_mul]
      rw [this]
      apply sum_lt_sum
      · intro i _
        apply sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left
        · trans ∑ i ∈ {i, j}, x i ^ 2
          · rw [sum_insert]
            simp
            simp at hj ⊢
            exact Fin.ne_of_lt hj
          · apply sum_le_sum_of_subset_of_nonneg
            · simp
            · intro _ _ _
              positivity
        · apply mul_nonneg <;> apply hx
      · use i, (by simp)
        apply sum_lt_sum
        · intro j hj
          apply mul_le_mul_of_nonneg_left
          · trans ∑ i ∈ {i, j}, x i ^ 2
            · rw [sum_insert]
              simp
              simp at hj ⊢
              apply Fin.ne_of_lt
              exact hj
            · apply sum_le_sum_of_subset_of_nonneg
              · simp
              · intro _ _ _
                positivity
          · apply mul_nonneg <;> apply hx
        · use j, (by simp [hij])
    contradiction

/- ∑ i < j, x i * x j * ∑ i, x i ^ 2 = 1 / 2 * (∑ i, x i ^ 2) * (∑ i < j, 2 * x i * x j) -/
lemma equality_2 {x : Fin n → ℝ}:
    (∑ i, ∑ j in Ioi i, x i * x j) * ∑ i, x i ^ 2 = (1 / 2) * ((∑ i, x i ^ 2) * ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) := by
  rw [mul_comm, mul_comm (1 / 2), mul_assoc]
  simp
  left
  rw [sum_mul]
  congr
  ext i
  rw [sum_mul]
  congr
  ext j
  field_simp
  ring

/- Applying the AM-GM inequality, we obtain that (∑ i, x i ^ 2) * (∑ i < j, 2 * x i * x j) ≤ (∑ i, xi^2 + ∑ i < j, 2xi * x j) ^ 2 / 4 -/
lemma am_gm_inequality {x : Fin n → ℝ} :
    (1 / 2) * ((∑ i, x i ^ 2) * ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) ≤ (1 / 8) * (∑ i, x i ^ 2 + ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) ^ 2 := by
  apply sub_nonneg.mp
  field_simp
  apply div_nonneg
  · trans 2 * (∑ i, x i ^ 2 - ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) ^ 2
    · positivity
    · apply le_of_eq
      ring
  · positivity

/- The AM-GM inequality holds if and only if ∑ i, x i ^ 2 = ∑ i < j, 2 * x i * xj --/
lemma am_gm_holds_of {x : Fin n → ℝ} (h : (1 / 2) * ((∑ i, x i ^ 2) * ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) = (1 / 8) * (∑ i, x i ^ 2 + ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) ^ 2) :
    ∑ i, x i ^ 2 = ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j := by
  apply sub_eq_zero.mpr at h
  field_simp at h
  apply sub_eq_zero.mp
  have h : (∑ i : Fin n, x i ^ 2 - ∑ i : Fin n, ∑ j ∈ Ioi i, 2 * x i * x j) ^ 2 * 2 = -0 := by
    rw [←h]
    ring
  simp at h
  exact h

/- ∑ i, xi^2 + ∑ i < j, 2xi * x j = (∑ i, x i) ^ 2 -/
lemma equality_3 {x : Fin n → ℝ} : (1 / 8) * (∑ i, x i ^ 2 + ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) ^ 2 = (1 / 8) * (∑ i, x i) ^ 4 := by
  rw [show 4 = 2 * 2 by ring]
  rw [pow_mul]
  congr
  rw [sq, sum_mul_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Fin.sum_univ_succ]
    simp [sum_add_distrib, ←ih]
    simp [←mul_sum, ←sum_mul]
    apply sub_eq_zero.mp
    ring_nf

/- We proved that if x has two equal element and equals to zero otherwise, then the equality holds -/
lemma eq_of_two_ne_zero {x : Fin n → ℝ} (h : ∃ i j, i < j ∧ x i = x j ∧ ∀ (k : Fin n), k ≠ i → k ≠ j → x k = 0) :
    ∑ i : Fin n, ∑ j ∈ Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) = (1 / 8) * (∑ i : Fin n, x i) ^ 4 := by
  obtain ⟨i, j, hij, heq, hzero⟩ := h
  let d := x i
  have hx' {k : Fin n} : x k = if k ≠ i ∧ k ≠ j then 0 else d := by
    by_cases hk : k ≠ i ∧ k ≠ j
    · simp [hk]
      apply hzero
      · exact hk.1
      · exact hk.2
    · simp [hk, d]
      simp at hk
      by_cases hk' : k = i
      · simp [hk']
      · apply hk at hk'
        simp [hk', heq]
  have : ∑ i, x i = 2 * d := by
    simp [hx', sum_ite]
    left
    norm_cast
    apply card_eq_two.mpr
    use i, j
    constructor
    · exact Fin.ne_of_lt hij
    · ext k
      simp
      tauto
  rw [this]
  have {i' j' : Fin n} : x i' * x j' * (x i' ^ 2 + x j' ^ 2) = if i' ∉ ({i, j} : Finset _) ∨ j' ∉ ({i, j} : Finset _) then 0 else 2 * d ^ 4 := by
    by_cases h : i' ∉ ({i, j} : Finset _) ∨ j' ∉ ({i, j} : Finset _)
    · simp only [if_pos h]
      simp
      left
      rcases h with (h | h)
      · left
        simp at h
        simp [hx', h]
      · right
        simp at h
        simp [hx', h]
    · simp only [if_neg h]
      simp at h
      obtain ⟨h₁, h₂⟩ := h
      by_cases h' : i' = i
      · simp [h']
        by_cases h'' : j' = i
        · simp [h'', d, heq]
          ring
        · apply h₂ at h''
          simp [h'', d, heq]
          ring
      · apply h₁ at h'
        simp [h']
        by_cases h'' : j' = i
        · simp [h'', d, heq]
          ring
        · apply h₂ at h''
          simp [h'', d, heq]
          ring
  have {i' : Fin n} : ∑ j ∈ Ioi i', x i' * x j * (x i' ^ 2 + x j ^ 2) = if i' = i then 2 * d ^ 4 else 0 := by
    simp [this, sum_ite]
    by_cases h : i' = i
    · simp [h]
      apply sub_eq_zero.mp
      nth_rw 2 [show 2 * d ^ 4 = 1 * (2 * d ^ 4) by ring]
      rw [←sub_mul]
      simp
      left
      apply sub_eq_zero.mpr
      norm_cast
      apply card_eq_one.mpr
      use j
      ext k
      simp
      constructor <;> intro hk
      · apply hk.2
        apply ne_of_gt hk.1
      · simp [hk]
        exact hij
    · simp [h]
      left
      apply filter_eq_empty_iff.mpr
      intro k hk
      simp at hk ⊢
      intro h
      rw [h] at hk
      constructor
      · apply ne_of_gt
        apply lt_trans hij hk
      · apply ne_of_gt hk
  simp [this]
  field_simp
  ring

/- 15. A1 (POL) ${ }^{\mathrm{IMO} 2}$ Let $n \geq 2$ be a fixed integer. Find the least constant $C$ such that the inequality  $$ \sum_{i< j} x_{i} x_{j}\left(x_{i}^{2}+x_{j}^{2}\right) \leq C\left(\sum_{i} x_{i}\right)^{4} $$  holds for every $x_{1}, \ldots, x_{n} \geq 0$ (the sum on the left consists of $\binom{n}{2}$ summands). For this constant $C$, characterize the instances of equality. -/
theorem inequalities_24904 {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {C | ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → ∑ i, ∑ j ∈ Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) ≤
    C * (∑ i, x i) ^ 4} (1 / 8) ∧ (∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, ∑ j ∈ Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) =
    (1 / 8) * (∑ i, x i) ^ 4 ↔ ∃ i j, i < j ∧ x i = x j ∧ ∀ k, k ≠ i → k ≠ j → x k = 0)) := by

  -- Applying all the lemmas we proved above, we can prove the main inequality
  have hle {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
      ∑ i, ∑ j in Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) ≤ (1 / 8) * (∑ i, x i) ^ 4 := by
    apply le_trans (inequalities_1 hx)
    rw [equality_2]
    apply le_trans am_gm_inequality
    apply le_of_eq
    exact equality_3

  constructor
  · -- Then we prove that 1/8 is the set.
    constructor
    · intro x hx
      apply hle hx
    · -- Then we show that 1 / 8 is the least constant.
      -- Given any C such that this inequality holds, We construct x 0 = x 1 = 1, and x i = 0 for i ≥ 2.
      intro C hC
      simp at hC
      let x : Fin n → ℝ := fun x => if x.1 ≤ 1 then 1 else 0
      -- By the lemma we proved above, we have that the inequality holds for this x.
      have hx : ∀ i, 0 ≤ x i := by
        intro i
        simp [x]
        split_ifs
        all_goals simp
      obtain hC := hC x hx
      have hx : ∃ i j, i < j ∧ x i = x j ∧ ∀ (k : Fin n), k ≠ i → k ≠ j → x k = 0 := by
        use ⟨0, Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩
        simp [x]
        intro k hk₁ hk₂
        by_contra h
        simp at h
        obtain ⟨k, hk⟩ := k
        interval_cases k
        · simp at hk₁
        · simp at hk₂
      obtain hx := eq_of_two_ne_zero hx
      rw [hx] at hC
      have : ∑ i, x i = 2 := by
        simp [x, sum_ite]
        norm_cast
        apply card_eq_two.mpr
        use ⟨0, by exact Nat.zero_lt_of_lt hn⟩, ⟨1, hn⟩
        simp
        ext ⟨i, hi⟩
        simp
        constructor <;> intro h
        · exact Nat.le_one_iff_eq_zero_or_eq_one.mp h
        · rcases h with h | h <;> simp [h]
      rw [this] at hC
      -- Therefore, 1 / 8 * 16 = C * 16
      simp at hC
      simp [hC]
  · intro x hx
    constructor <;> intro h
    · -- If the equality holds, we obtain that
      -- 1. ∑ i < j, x i * x j * (x i ^ 2 + x j ^ 2) = (∑ i < j, x i * x j) * ∑ i, x i ^ 2
      have h₁ : ∑ i : Fin n, ∑ j ∈ Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) = (∑ i, ∑ j in Ioi i, x i * x j) * ∑ i, x i ^ 2 := by
        apply le_antisymm
        · apply inequalities_1 hx
        · rw [h, equality_2, ←equality_3]
          apply am_gm_inequality
      -- 2. (∑ i, x i ^ 2) * (∑ i < j, 2 * x i * x j) = (∑ i, x i ^ 2 + ∑ i < j, 2 * x i * x j) ^ 2 / 4
      have h₂ : (1 / 2) * ((∑ i, x i ^ 2) * ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) = (1 / 8) * (∑ i, x i ^ 2 + ∑ i, ∑ j ∈ Ioi i, 2 * x i * x j) ^ 2 := by
        apply le_antisymm
        · apply am_gm_inequality
        · rw [←equality_2, equality_3, ←h, h₁]
      -- Then we obtain that
      -- 1. ∃ i j, i ≠ j ∧ ∀ (k : Fin n), k ≠ i → k ≠ j → x k = 0
      apply inequalities_1_holds_of hn hx at h₁
      -- 2. ∑ i, x i ^ 2 = ∑ i < j, 2 * x i * x j
      apply am_gm_holds_of at h₂
      obtain ⟨i, j, hij, hx⟩ := h₁
      -- wlog, we assume that i < j
      wlog h : i < j generalizing i j with H
      · simp at h
        have : j < i := by
          apply lt_of_le_of_ne
          · exact h
          · apply Ne.symm
            assumption
        exact H j i (Ne.symm hij) (by intro k h₁ h₂; apply hx _ h₂ h₁) this
      · use i, j, h
        -- Then we only need to show that x i = x j
        -- Note that ∑ x i ^ 2 = xi ^ 2 + xj ^ 2
        constructor
        · let d₁ := x i
          let d₂ := x j
          have hx {k : Fin n} : x k = if k = i then d₁ else if k = j then d₂ else 0 := by
            by_cases hk : k = i
            · simp [hk]
            · by_cases hk' : k = j
              · simp [hk', Ne.symm hij]
              · simp [hk, hk']
                apply hx k hk hk'
          have : ∑ i, x i ^ 2 = d₁ ^ 2 + d₂ ^ 2 := by
            simp [hx, sum_ite, Ne.symm hij]
            apply mul_left_eq_self₀.mpr
            left
            norm_cast
            apply card_eq_one.mpr
            use i
            ext k
            simp
          rw [this] at h₂
          -- and ∑ i < j, 2 * x i * x j = 2 * d₁ * d₂
          have {i': Fin n} : ∑ j ∈ Ioi i', 2 * x i' * x j = if i' = i then 2 * d₁ * d₂ else 0 := by
            simp [hx, sum_ite]
            by_cases hi' : i' = i
            · simp [hi', h, Ne.symm hij]
              left
              apply filter_eq_empty_iff.mpr
              intro k hk
              simp at hk
              exact Fin.ne_of_gt hk
            · simp [hi']
              by_cases hj : i' = j
              · simp [hj]
                left
                apply filter_eq_empty_iff.mpr
                intro k hk
                simp at hk
                apply Fin.ne_of_gt
                apply lt_trans h hk
              · simp [hj]
          simp [this, sum_ite_eq] at h₂
          -- We obtain that d₁ ^ 2 + d₂ ^ 2 = 2 * d₁ * d₂, which implies that d₁ = d₂
          have : (d₁ - d₂) ^ 2 = 0 := by
            rw [sub_sq]
            rw [←h₂]
            ring
          simp at this
          apply sub_eq_zero.mp this
        · exact hx
    · apply eq_of_two_ne_zero h
