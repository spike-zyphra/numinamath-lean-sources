import Mathlib

/- 2. let $M$ be a finite set of real numbers with the following property: From every three different elements of $M$, two can always be selected whose sum lies in $M$. What is the maximum number of elements $M$ can have?

## Solution -/
theorem number_theory_263317: IsGreatest {u: ℕ | ∃ (M: Finset ℝ), u = M.card ∧
  (∀ x ∈ M, ∀ y ∈ M, ∀ z ∈ M, x ≠ y ∧ y ≠ z ∧ z ≠ x →
    ∃ a ∈ M, a = x + y ∨ a = y + z ∨ a = x + z)
  } 7 := by

  -- if x > second largest elements of set s, then x is the maximal elements.
  have eq_of_gt_max_erase {s: Finset ℝ} {a b:ℝ} (x:ℝ)
    (hx1: x > b) (hx2: x ∈ s)
    (hb: (s.erase a).max = b):
    x = a := by
    replace hx1: x ∉ s.erase a := by
      rintro h
      absurd hx1; push_neg
      apply Finset.le_max_of_eq h hb
    by_contra!
    absurd hx1
    rw [Finset.mem_erase]
    exact ⟨this, hx2⟩

  -- if x is maximal, then any y ∈ s.erase x, y < x
  have lt_max_of_mem_erase {x y: ℝ} {s: Finset ℝ}
    (hx: s.max = x) (hy: y ∈ s.erase x):
    y < x := by
    apply lt_of_le_of_ne ?_ ?_
    · apply Finset.le_max_of_eq ?_ hx
      exact Finset.mem_of_mem_erase hy
    · exact Finset.ne_of_mem_erase hy

  -- similarly, if x < second smallest elements of set s, x is the minimal.
  have eq_of_lt_min_erase {s: Finset ℝ} {a b:ℝ} (x:ℝ)
    (hx1: x < b) (hx2: x ∈ s)
    (hb: (s.erase a).min = b):
    x = a := by
    replace hx1: x ∉ s.erase a := by
      rintro h
      absurd hx1; push_neg
      apply Finset.min_le_of_eq h hb
    by_contra!
    absurd hx1
    rw [Finset.mem_erase]
    exact ⟨this, hx2⟩

  -- if x is minimal, any y ∈ s.erase x, y > x
  have min_lt_of_mem_erase {x y: ℝ} {s: Finset ℝ}
    (hx: s.min = x) (hy: y ∈ s.erase x):
    x < y := by
    apply lt_of_le_of_ne ?_ ?_
    · apply Finset.min_le_of_eq ?_ hx
      exact Finset.mem_of_mem_erase hy
    · exact (Finset.ne_of_mem_erase hy).symm

  rw [IsGreatest, upperBounds]
  simp only [ne_eq, and_imp, Set.mem_setOf_eq, forall_exists_index]

  constructor

  · -- find such M.
    -- a possible solution is {-3,-2,-1,0,1,2,3}
    use {-3,-2,-1,0,1,2,3}
    refine ⟨(by norm_num), ?_⟩
    clear * -
    norm_num

  · -- prove any set satisfy the property cannot have more than 7 elements.
    rintro _ M rfl hM

    -- M has positive parts and negative parts.
    set M1: Finset ℝ := Finset.filter (· ≥ 0) M with M1_def
    set M2: Finset ℝ := Finset.filter (· < 0) M with M2_def
    have M_of_M1M2: M = M1 ∪ M2 := by
      ext x
      simp only [M1_def, ge_iff_le, M2_def,
      Finset.mem_union, Finset.mem_filter]
      have: 0 ≤ x ∨ x < 0 := le_or_lt 0 x
      clear * - this
      tauto
    have hMcard: M.card = M1.card + M2.card := by
      have: Disjoint M1 M2 := by
        refine Finset.disjoint_filter.mpr ?_
        intro _ _
        simp only [ge_iff_le, not_lt, imp_self]
      rw [M_of_M1M2, Finset.card_union_of_disjoint this]

    -- any elements in M1 ≥ 0
    have nng_of_M1 (x:ℝ) (hx: x ∈ M1): 0 ≤ x := by
      simp only [M1_def, ge_iff_le, Finset.mem_filter] at hx
      exact hx.right

    -- elements in M1 also in M
    have mem_M1 {x:ℝ} (hx: x ∈ M1): x ∈ M := by
      simp only [M1_def, ge_iff_le, Finset.mem_filter] at hx
      exact hx.left

    -- any elments in M2 < 0
    have neg_of_M2 (x:ℝ) (hx: x ∈ M2): x < 0 := by
      simp only [M2_def, Finset.mem_filter] at hx
      exact hx.right

    -- elements in M2 also in M
    have mem_M2 {x:ℝ} (hx: x ∈ M2): x ∈ M := by
      simp only [M2_def, Finset.mem_filter] at hx
      exact hx.left

    -- if a is the maximal and b the second largest elements in M1,
    -- if one of a+b,b+c,a+c is in M, then either c=0 or a = b+c
    have case_M1 {a b c: ℝ}
      (ha: a ∈ M1) (hb: b ∈ M1) (hc: c ∈ M1)
      (maxa: M1.max = a) (maxb: (M1.erase a).max = b)
      (hab: a ≠ b)(hbc: b ≠ c)(hca: c ≠ a):
      a = b+c ∨ c = 0 := by
      replace maxa: ∀x ∈ M, x ≤ a := by
        simp only [M_of_M1M2, Finset.mem_union]
        intro x
        rintro (hx1 | hx2)
        · apply Finset.le_max_of_eq hx1 maxa
        · simp only [M2_def, Finset.mem_filter] at hx2
          apply le_trans hx2.right.le (nng_of_M1 a ha)
      have cltb: c < b := by
        apply lt_of_le_of_ne ?_ hbc.symm
        apply Finset.le_max_of_eq ?_ maxb
        exact Finset.mem_erase_of_ne_of_mem hca hc
      have bpos: 0 < b := by
        apply lt_of_le_of_lt ?_ cltb
        apply nng_of_M1 c hc
      specialize hM a (mem_M1 ha) b (mem_M1 hb) c (mem_M1 hc)
        hab hbc hca
      rcases hM with ⟨d,hd1, hd2⟩
      specialize maxa d hd1
      rcases hd2 with hh | hh | hh
      · rw [hh] at maxa
        linarith only [maxa, bpos]
      · by_cases cz: c = 0
        · right; exact cz
        push_neg at cz
        have cpos: 0 < c := by
          apply lt_of_le_of_ne ?_ cz.symm
          apply nng_of_M1 c hc
        left; rw [← hh]; symm
        have hd3: d ∈ M1 := by
          simp only [M1_def, ge_iff_le, Finset.mem_filter,
          hd1, true_and]
          linarith only [hh, bpos, cpos]
        have hd4: d > b := by
          rw [hh]
          linarith only [cpos]
        apply eq_of_gt_max_erase d hd4 hd3 maxb
      · right
        rw [hh] at maxa
        linarith only [maxa, nng_of_M1 c hc]

    -- then cardinal of M1 ≤ 4
    have hM1: M1.card ≤ 4 := by

      -- take a > b > c > d.
      by_cases h1: M1 = ∅
      · simp [h1]
      replace h1 := Finset.nonempty_iff_ne_empty.mpr h1
      rcases (Finset.max_of_nonempty h1) with ⟨a,ha⟩
      have ha1: a ∈ M1 := Finset.mem_of_max ha

      by_cases h2: (M1.erase a) = ∅
      · simp [← Finset.card_erase_add_one ha1, h2]
      replace h2 := Finset.nonempty_iff_ne_empty.mpr h2
      rcases (Finset.max_of_nonempty h2) with ⟨b,hb⟩
      have hb1: b ∈ M1.erase a := Finset.mem_of_max hb
      have hba: b < a := lt_max_of_mem_erase ha hb1
      have hb2: b ∈ M1 := Finset.mem_of_mem_erase hb1

      by_cases h3: (M1.erase a).erase b = ∅
      · simp [← Finset.card_erase_add_one ha1,
        ← Finset.card_erase_add_one hb1, h3]
      replace h3 := Finset.nonempty_iff_ne_empty.mpr h3
      rcases (Finset.max_of_nonempty h3) with ⟨c,hc⟩
      have hc1: c ∈ (M1.erase a).erase b := Finset.mem_of_max hc
      have hcb: c < b := lt_max_of_mem_erase hb hc1
      have hc2: c ∈ M1 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc1)

      by_cases h4: ((M1.erase a).erase b).erase c = ∅
      · simp [← Finset.card_erase_add_one ha1,
        ← Finset.card_erase_add_one hb1, ← Finset.card_erase_add_one hc1, h4]
      replace h4 := Finset.nonempty_iff_ne_empty.mpr h4
      rcases (Finset.max_of_nonempty h4) with ⟨d,hd⟩
      have hd1: d ∈ ((M1.erase a).erase b).erase c := Finset.mem_of_max hd
      have hdc: d < c := lt_max_of_mem_erase hc hd1
      have hd2: d ∈ M1 := Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd1))

      -- c ≠ 0, since 0 ≤ d < c
      have cpos: 0 < c := by
        apply lt_of_le_of_lt ?_ hdc
        apply nng_of_M1 d hd2
      -- then a = b+c
      have aeq: a = b+c := by
        specialize case_M1 ha1 hb2 hc2 ha hb
          hba.ne' hcb.ne' (hcb.trans hba).ne
        simp only [cpos.ne', or_false] at case_M1
        exact case_M1
      -- a ≠ b+d since c ≠ d
      have ane: a ≠ b+d := by
        rw [aeq]
        simp [hdc.ne']
      -- then d = 0
      have deq: d = 0 := by
        specialize case_M1 ha1 hb2 hd2 ha hb
          hba.ne' (hdc.trans hcb).ne' ((hdc.trans hcb).trans hba).ne
        simp only [ane, false_or] at case_M1
        exact case_M1

      -- then the set cannot contain another element, otherwise contradicts d=0
      have h5: (((M1.erase a).erase b).erase c).erase d = ∅ := by
        by_contra!
        replace := Finset.nonempty_iff_ne_empty.mpr this
        rcases (this.exists_mem) with ⟨e,he⟩
        have he1: e < 0 := by
          rw [← deq]
          apply lt_max_of_mem_erase hd he
        have he2: 0 ≤ e := by
          apply nng_of_M1 e ?_
          clear * - he
          simp_all only [ge_iff_le, Finset.mem_erase, ne_eq,
          Finset.mem_filter, and_self, M1]
        linarith only [he1, he2]
      -- therefore cardinal ≤ 4
      simp [← Finset.card_erase_add_one ha1, ← Finset.card_erase_add_one hb1,
      ← Finset.card_erase_add_one hc1, ← Finset.card_erase_add_one hd1, h5]

    -- similarly, if a is minimal and b second least elements in M2,
    -- if one of a+b,b+c,a+c is in M, then a=b+c
    have case_M2 {a b c: ℝ}
      (ha: a ∈ M2) (hb: b ∈ M2) (hc: c ∈ M2)
      (mina: M2.min = a) (minb: (M2.erase a).min = b)
      (hab: a ≠ b)(hbc: b ≠ c)(hca: c ≠ a):
      a = b+c := by
      replace mina: ∀x ∈ M, a ≤ x := by
        simp only [M_of_M1M2, Finset.mem_union]
        intro x
        rintro (hx1 | hx2)
        · apply le_trans (neg_of_M2 a ha).le (nng_of_M1 x hx1)
        · apply Finset.min_le_of_eq hx2 mina
      have cgtb: c > b := by
        apply lt_of_le_of_ne ?_ hbc
        apply Finset.min_le_of_eq ?_ minb
        exact Finset.mem_erase_of_ne_of_mem hca hc
      specialize hM a (mem_M2 ha) b (mem_M2 hb) c (mem_M2 hc)
        hab hbc hca
      rcases hM with ⟨d,hd1, hd2⟩
      specialize mina d hd1
      rcases hd2 with hh | hh | hh
      · rw [hh] at mina
        linarith only [mina, neg_of_M2 b hb]
      · have hd3: d ∈ M2 := by
          simp only [M2_def, ge_iff_le, Finset.mem_filter,
          hd1, true_and]
          linarith only [hh, neg_of_M2 b hb, neg_of_M2 c hc]
        have hd4: d < b := by
          rw [hh]
          linarith only [neg_of_M2 c hc]
        rw [← hh]; symm
        apply eq_of_lt_min_erase d hd4 hd3 minb
      · rw [hh] at mina
        linarith only [mina, neg_of_M2 c hc]

    have hM2: M2.card ≤ 3 := by

      -- take a < b < c
      by_cases h1: M2 = ∅
      · simp [h1]
      replace h1 := Finset.nonempty_iff_ne_empty.mpr h1
      rcases (Finset.min_of_nonempty h1) with ⟨a,ha⟩
      have ha1: a ∈ M2 := Finset.mem_of_min ha

      by_cases h2: (M2.erase a) = ∅
      · simp [← Finset.card_erase_add_one ha1, h2]
      replace h2 := Finset.nonempty_iff_ne_empty.mpr h2
      rcases (Finset.min_of_nonempty h2) with ⟨b,hb⟩
      have hb1: b ∈ M2.erase a := Finset.mem_of_min hb
      have hba: a < b := min_lt_of_mem_erase ha hb1
      have hb2: b ∈ M2 := Finset.mem_of_mem_erase hb1

      by_cases h3: (M2.erase a).erase b = ∅
      · simp [← Finset.card_erase_add_one ha1,
        ← Finset.card_erase_add_one hb1, h3]
      replace h3 := Finset.nonempty_iff_ne_empty.mpr h3
      rcases (Finset.min_of_nonempty h3) with ⟨c,hc⟩
      have hc1: c ∈ (M2.erase a).erase b := Finset.mem_of_min hc
      have hcb: b < c := min_lt_of_mem_erase hb hc1
      have hc2: c ∈ M2 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc1)

      -- since c < 0, we get a = b+c
      have aeq: a = b+c := case_M2 ha1 hb2 hc2 ha hb
        hba.ne hcb.ne (hba.trans hcb).ne'

      -- then we claim cannot take another d, otherwise d = 0, contradiction.
      have h4: ((M2.erase a).erase b).erase c = ∅ := by
        by_contra!
        replace := Finset.nonempty_iff_ne_empty.mpr this
        rcases (this.exists_mem) with ⟨d,hd1⟩
        have hdc: c < d := min_lt_of_mem_erase hc hd1
        have hd2: d ∈ M2 := Finset.mem_of_mem_erase
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd1))
        have aeq': a = b+d := case_M2 ha1 hb2 hd2 ha hb hba.ne
          (hcb.trans hdc).ne (hba.trans ((hcb.trans) hdc)).ne'
        simp [aeq, hdc.ne] at aeq'
      -- therefore cardinal ≤ 3
      simp [← Finset.card_erase_add_one ha1, ← Finset.card_erase_add_one hb1,
      ← Finset.card_erase_add_one hc1, h4]

    -- then cardinal add ≤ 7
    rw [hMcard]
    linarith only [hM1, hM2]