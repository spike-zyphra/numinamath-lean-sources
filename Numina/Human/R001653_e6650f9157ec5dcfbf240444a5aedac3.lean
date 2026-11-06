import Mathlib

open Polynomial Finset

/- For any integer k, if k ∣ 2, then k ∣ 1 ∨ k = -2 ∨ k = 2 -/
lemma cases_dvd_2 {k : ℤ} (hk : k ∣ 2) : k ∣ 1 ∨ |k| = 2 := by
  obtain ⟨a, ha⟩ := hk
  by_cases h : 2 ∣ a
  · obtain ⟨b, hb⟩ := h
    rw [hb] at ha
    left
    use b
    apply sub_eq_zero.mpr at ha
    have : 2 * (1 - k * b) = 0 := by rw [←ha]; ring
    simp at this
    exact Int.eq_of_sub_eq_zero this
  · right
    apply Int.dvd_antisymm
    · simp
    · simp
    · rw [ha]
      have hk : |k| ∣ k := by exact abs_dvd_self k
      exact Dvd.dvd.mul_right hk a
    · apply IsCoprime.dvd_of_dvd_mul_right (z := a)
      · have h : Odd a := by
          refine Int.not_even_iff_odd.mp ?_
          by_contra h
          have : 2 ∣ a := by exact even_iff_two_dvd.mp h
          contradiction
        have h : 2 ∣ a + 1 := by
          have h : Even (a + 1) := by
            exact Odd.add_one h
          exact even_iff_two_dvd.mp h
        obtain ⟨b, hb⟩ := h
        rw [IsCoprime]
        use b, -1
        simp
        rw [mul_comm, ←hb]
        ring
      · rw [ha]
        refine Int.mul_dvd_mul_right a ?_
        exact self_dvd_abs k

/- We show that if ∏ z ∈ s, f z ∣ 1, where f is an injection, then |s| ≤ 2, where is done by showing f z ∈ {-1, 2} -/
lemma card_le_two_of_prod_dvd_one {s : Finset ℤ} {f : ℤ → ℤ} (hs : ∏ z ∈ s, f z ∣ 1) (hf : Function.Injective f) : s.card ≤ 2 := by
  let g := Function.invFun f
  have hg : g ∘ f = id := by exact Function.invFun_comp hf
  have : s ⊆ {g 1, g (-1)} := by
    intro z hz
    simp
    obtain h:= congrFun hg z
    simp at h
    rw [←h]
    have h : f z ∣ 1 := by
      apply dvd_trans ?_ hs
      exact dvd_prod_of_mem f hz
    by_cases h1 : f z ≥ 0
    · left
      apply Int.eq_one_of_dvd_one h1 at h
      rw [←h]
    · right
      have h2 : -(f z) ≥ 0 := by
        simp at h1 ⊢
        exact le_of_lt h1
      have h : -(f z) ∣ 1 := by exact Int.neg_dvd.mpr h
      apply Int.eq_one_of_dvd_one h2 at h
      congr
      rw [eq_comm, Int.neg_eq_comm, h]
  apply card_le_card at this
  apply le_trans this
  exact card_le_two

/- We show that if ∏ z ∈ s, f z ∣ 2, where f is an injection, then |s| ≤ 3. -/
lemma card_le_three_of_prod_dvd_two {s : Finset ℤ} {f : ℤ → ℤ} (hs : ∏ z ∈ s, f z ∣ 2) (hf : Function.Injective f) : s.card ≤ 3 := by
  -- by the first lemma, we have ∏ z ∈ s, |f z| ∣ 1 ∨ ∏ z ∈ s, |f z| = 2
  rcases cases_dvd_2 hs with h | h
  · -- if ∏ z ∈ s, |f z| ∣ 1, then |s| ≤ 2 by the second lemma
    trans 2
    · exact card_le_two_of_prod_dvd_one h hf
    · simp
  · -- otherwise, 2 or -2 is in the image of f, so we can find an element z such that |f z| = 2
    -- Remove z, we have ∏ z ∈ s.erase z, |f z| ∣ 1. Again, by the second lemma, we have |s.erase z| ≤ 2
    rw [abs_prod] at h
    have ⟨z, hz, heq⟩ : ∃ z ∈ s, |f z| = 2 := by
      by_contra hz
      simp at hz
      by_cases hle : ∀ x ∈ s, |f x| ≤ 1
      · have : ∏ x ∈ s, |f x| ≤ ∏ _ ∈ s, (1 : ℤ) := by
          apply prod_le_prod
          · intro x hx
            simp
          · intro i hi
            apply hle i hi
        simp [h] at this
      · simp at hle
        obtain ⟨x, hx, hxlt⟩ := hle
        have hxlt : 2 < |f x| := by
          apply lt_of_le_of_ne
          · exact hxlt
          · exact fun a ↦ hz x hx (id (Eq.symm a))
        have : |f x| ≤ ∏ z ∈ s, |f z| := by
          apply Int.le_of_dvd
          · simp [h]
          · exact dvd_prod_of_mem (fun i ↦ |f i|) hx
        apply lt_of_lt_of_le hxlt at this
        simp [h] at this
    have hunion : s = {z} ∪ s.erase z := by
      rw [union_erase_of_mem, union_eq_right.mpr]
      exact singleton_subset_iff.mpr hz
      simp
    rw [hunion, prod_union] at h
    · rw [hunion]
      simp
      rw [show 3 = 1 + 2 by simp]
      gcongr
      simp [heq] at h
      apply card_le_two_of_prod_dvd_one ?_ hf
      have h : ∏ x ∈ s.erase z, |f x| ∣ 1 := by simp [h]
      rw [←abs_prod] at h
      exact (abs_dvd_abs (∏ z ∈ s.erase z, f z) 1).mp h
    · simp

/- We show that if (P - 1)(x) = 0, then P + 1 has at most 3 distinct roots -/
lemma card_nodup_roots_le_three {P : ℤ[X]} (x : ℤ) (hx : (P - 1).IsRoot x) : (P + 1).roots.toFinset.card ≤ 3 := by
  -- It is easy to show that ∏ z ∈ (P + 1).roots.toFinset, (x - z) ∣ P x + 1 = 2
  have hdvd : ∏ z ∈ (P + 1).roots.toFinset, (X - C z) ∣ P + 1 := by
    apply dvd_trans ?_ (prod_multiset_X_sub_C_dvd (P + 1))
    rw [prod_multiset_root_eq_finset_root]
    apply prod_dvd_prod_of_dvd
    intro z hz
    apply dvd_pow_self
    apply ne_of_gt
    simp only [Multiset.mem_toFinset, mem_roots'] at hz
    apply rootMultiplicity_pos hz.1 |>.mpr hz.2

  apply eval_dvd (x := x) at hdvd
  simp at hdvd hx
  apply sub_eq_zero.mp at hx
  simp [hx, eval_prod] at hdvd

  -- Apply the lemma above, we have that the roots of P + 1 are at most 3
  apply card_le_three_of_prod_dvd_two hdvd ?_
  exact sub_right_injective

/- Similarly, if (P + 1)(x) = 0, then P - 1 has at most 3 distinct roots -/
lemma card_nodup_roots_le_three' {P : ℤ[X]} (x : ℤ) (hx : (P + 1).IsRoot x) : (P - 1).roots.toFinset.card ≤ 3 := by
  have hdvd : ∏ z ∈ (P - 1).roots.toFinset, (X - C z) ∣ P - 1 := by
    apply dvd_trans ?_ (prod_multiset_X_sub_C_dvd (P - 1))
    rw [prod_multiset_root_eq_finset_root]
    apply prod_dvd_prod_of_dvd
    intro z hz
    apply dvd_pow_self
    apply ne_of_gt
    simp only [Multiset.mem_toFinset, mem_roots'] at hz
    apply rootMultiplicity_pos hz.1 |>.mpr hz.2

  apply eval_dvd (x := x) at hdvd
  simp at hdvd hx
  have hx : eval x P = -1 := by exact (Int.add_left_inj 1).mp hx
  simp [hx, eval_prod] at hdvd

  apply card_le_three_of_prod_dvd_two hdvd ?_
  exact sub_right_injective

/- We can also observe that if (P - 1)(x) = 0, (P + 1) has 3 distinct roots (a b c), then x - max(a,b,c) ≥ 1 -/
lemma sub_min'_ge_one {P : ℤ[X]} (x : ℤ) (hx : (P - 1).IsRoot x) (h : (P + 1).roots.toFinset.card = 3) : x - (P + 1).roots.toFinset.min' (by by_contra h'; simp at h'; simp [h'] at h) ≥ 1 := by
  -- we show that ∀ z such that P(z) = -1, x - z ∣ 2
  have hdvd : ∏ z ∈ (P + 1).roots.toFinset, (X - C z) ∣ P + 1 := by
    apply dvd_trans ?_ (prod_multiset_X_sub_C_dvd (P + 1))
    rw [prod_multiset_root_eq_finset_root]
    apply prod_dvd_prod_of_dvd
    intro z hz
    apply dvd_pow_self
    apply ne_of_gt
    simp only [Multiset.mem_toFinset, mem_roots'] at hz
    apply rootMultiplicity_pos hz.1 |>.mpr hz.2

  apply eval_dvd (x := x) at hdvd
  simp at hdvd hx
  apply sub_eq_zero.mp at hx
  simp [hx, eval_prod] at hdvd

  -- then there are four cases, x - z ∈ {-2, -1, 1, 2}
  -- By contradiction, if for any z, x - z < 1, then x - z ∈ {-2, -1}, P + 1 has at most 2 roots, which contradicts the assumption
  by_contra hlt
  simp at hlt
  have hlt {z : ℤ} (hz : z ∈ (P + 1).roots.toFinset) : x - z < 1 := by
    apply lt_of_le_of_lt ?_ hlt
    gcongr
    apply min'_le
    exact hz
  have hdvd {z : ℤ} (hz : z ∈ (P + 1).roots.toFinset) : x - z ∣ 2 := by
    apply dvd_trans ?_ hdvd
    exact dvd_prod_of_mem (HSub.hSub x) hz

  have hge {z : ℤ} (hz : z ∈ (P + 1).roots.toFinset) : x - z ∈ ({-1, -2} : Finset ℤ) := by
    obtain hdvd := hdvd hz
    apply cases_dvd_2 at hdvd
    rcases hdvd with h | h
    · have : |x -z| ∣ 1 := by exact (abs_dvd (x - z) 1).mpr h
      apply Int.eq_one_of_dvd_one (by positivity) at this
      rw [abs_eq (by positivity)] at this
      rcases this with h | h
      · have hlt := hlt hz
        simp [h] at hlt
      · simp [h]
    · rw [abs_eq (by positivity)] at h
      rcases h with h | h
      · have : x - z < 1 := by apply hlt hz
        simp [h] at this
      · simp [h]

  have hsub : (P + 1).roots.toFinset ⊆ {x + 1, x + 2} := by
    intro z hz
    obtain hge := hge hz
    simp at hge
    rcases hge with h | h <;> simp
    · left
      linarith only [h]
    · right
      linarith only [h]

  apply card_le_card at hsub
  simp [h] at hsub

/- We prove that if (P-1)(x)=0, and (P+1)(y)=0, then x - y ≤ 2 -/
lemma sub_le_two {P : ℤ[X]} (x : ℤ) (hx : (P - 1).IsRoot x) (y : ℤ) (hy : y ∈ (P + 1).roots.toFinset) : x - y ≤ 2 := by
  -- We show that x - y ∣ P + 1 = 2
  have hdvd : ∏ z ∈ (P + 1).roots.toFinset, (X - C z) ∣ P + 1 := by
    apply dvd_trans ?_ (prod_multiset_X_sub_C_dvd (P + 1))
    rw [prod_multiset_root_eq_finset_root]
    apply prod_dvd_prod_of_dvd
    intro z hz
    apply dvd_pow_self
    apply ne_of_gt
    simp only [Multiset.mem_toFinset, mem_roots'] at hz
    apply rootMultiplicity_pos hz.1 |>.mpr hz.2

  apply eval_dvd (x := x) at hdvd
  simp at hdvd hx
  apply sub_eq_zero.mp at hx
  simp [hx, eval_prod] at hdvd
  -- then x - y ≤ 2
  have : x - y ∣ 2 := by
    apply dvd_trans ?_ hdvd
    exact dvd_prod_of_mem (HSub.hSub x) hy

  apply Int.le_of_dvd ?_ this
  simp

/- We show that if (P +1) has exact three distinct roots, then (P-1) has at most 2 distinct roots -/
lemma card_nodup_roots_le_two {P : ℤ[X]} (h : (P + 1).roots.toFinset.card = 3) : (P - 1).roots.toFinset.card ≤ 2 := by
  by_cases hP : (P - 1).roots.toFinset.Nonempty
  · -- wlog, we assume that (P-1) has at least one root z
    -- Let m, M be the minimum and maximum of (P - 1)'s roots'
    let m := (P - 1).roots.toFinset.min' hP
    let M := (P - 1).roots.toFinset.max' hP
    let x := (P + 1).roots.toFinset.min' (by by_contra h'; simp at h'; simp [h'] at h)
    have hm : (P - 1).IsRoot m := by
      suffices hm : m ∈ (P - 1).roots.toFinset
      · simp only [Multiset.mem_toFinset] at hm
        exact isRoot_of_mem_roots hm
      · exact min'_mem (P - 1).roots.toFinset hP
    have hM : (P - 1).IsRoot M := by
      suffices hM : M ∈ (P - 1).roots.toFinset
      · simp only [Multiset.mem_toFinset] at hM
        exact isRoot_of_mem_roots hM
      · exact max'_mem (P - 1).roots.toFinset hP
    have hx : x ∈ (P + 1).roots.toFinset := by apply min'_mem
    -- by the lemma above, we have that m - x ≥ 1, and M - x ≤ 2
    -- therefore x + 1 ≤ m ≤ z ≤ M ≤ x + 2
    obtain hm := sub_min'_ge_one m hm h
    obtain hM := sub_le_two M hM x hx
    have : (P - 1).roots.toFinset ⊆ Icc (x + 1) (x + 2) := by
      intro z hz
      simp
      constructor
      · trans m
        · linarith only [hm]
        · apply min'_le
          exact hz
      · trans M
        · apply le_max'
          exact hz
        · linarith only [hM]
    -- The roots of (P - 1) are in the interval [x + 1, x + 2], so there are at most 2 roots
    apply card_le_card at this
    simp at this
    exact this
  · simp at hP
    simp [hP]

/- 3. I 3 (SWE 3) ${ }^{\mathrm{IMO}}$ Let $P$ be a non-constant polynomial with integer coefficients. If $n(P)$ is the number of distinct integers $k$ such that $(P(k))^2=1,$ prove that $n(P)-\deg(P)\le2,$ where $\deg(P)$ denotes the degree of the polynomial $P.$ -/
theorem algebra_25019 {P : Polynomial ℤ} (hP : ∀ c : ℤ, P ≠ c) (n : ℕ) (hn : n = {k : ℤ | P.eval k ^ 2 = 1}.ncard) :
    n - P.natDegree ≤ 2 := by
  -- P(k) ^ 2= 1 ↔ P(k) = 1 ∨ P(k) = -1
  have hroot : {k : ℤ | P.eval k ^ 2 = 1} = (P - 1).roots.toFinset ∪ (P + 1).roots.toFinset := by
    ext k
    simp
    constructor <;> intro h
    · rcases h with h | h
      · left
        constructor
        · exact sub_ne_zero_of_ne (hP One.one)
        · simp [h]
      · right
        constructor
        · obtain h' := hP (-1)
          simp at h'
          intro hP
          have hP : P = -1 := by exact Eq.symm (neg_eq_of_add_eq_zero_left hP)
          contradiction
        · simp [h]
    · rcases h with ⟨_, h⟩ | ⟨_, h⟩
      · left
        exact (Int.add_left_inj (-1)).mp h
      · right
        exact (Int.add_left_inj 1).mp h

  rw [hroot] at hn
  rw [Set.ncard_coe_Finset] at hn
  by_cases hP : P.natDegree ≤ 2
  · -- 3. For $\operatorname{deg}(P) \leq 2$ the statement is obvious, since $n(P) \leq \operatorname{deg}\left(P^{2}\right)=$ $2 \operatorname{deg}(P) \leq \operatorname{deg}(P)+2$ 。
    simp [hn]
    trans (P - 1).natDegree + (P + 1).natDegree
    · apply le_trans (card_union_le _ _)
      gcongr
      · trans (P - 1).roots.card
        · exact Multiset.toFinset_card_le (P - 1).roots
        · exact card_roots' (P - 1)
      · trans (P + 1).roots.card
        · exact Multiset.toFinset_card_le (P + 1).roots
        · exact card_roots' (P + 1)
    · trans P.natDegree + P.natDegree
      · gcongr
        · apply le_trans (natDegree_sub_le _ _)
          simp
        · apply le_trans (natDegree_add_le _ _)
          simp
      · gcongr
  · -- Suppose now that $\operatorname{deg}(P) \geq 3$
    simp at hP
    by_cases h_neg_one : (P + 1).roots.toFinset = ∅
    · -- if (P + 1)(x) = 0 has no roots or (P - 1)(x) = 0 has no roots, then we have n(P) ≤ deg(P)
      simp [h_neg_one] at hn
      simp [hn]
      trans (P - 1).natDegree
      · trans (P - 1).roots.card
        · exact Multiset.toFinset_card_le (P - 1).roots
        · exact card_roots' (P - 1)
      trans P.natDegree
      · apply le_trans (natDegree_sub_le _ _)
        simp
      · simp
    · by_cases h_one : (P - 1).roots.toFinset = ∅
      · simp [h_one] at hn
        rw [hn]
        simp
        trans (P + 1).natDegree
        · trans (P + 1).roots.card
          · exact Multiset.toFinset_card_le (P + 1).roots
          · exact card_roots' (P + 1)
        trans P.natDegree
        · apply le_trans (natDegree_add_le _ _)
          simp
        · simp
      · -- Otherwise, by the lemmas, we have that (P - 1)(x) = 0 has at most 3 roots, and (P + 1)(x) = 0 has at most 3 roots
        simp [hn]
        obtain ⟨a, ha⟩ : (P + 1).roots.toFinset.Nonempty := by exact nonempty_iff_ne_empty.mpr h_neg_one
        obtain ⟨b, hb⟩ : (P - 1).roots.toFinset.Nonempty := by exact nonempty_iff_ne_empty.mpr h_one
        have ha : (P - 1).roots.toFinset.card ≤ 3 := by
          apply card_nodup_roots_le_three' a
          simp only [Multiset.mem_toFinset] at ha
          exact isRoot_of_mem_roots ha
        have hb : (P + 1).roots.toFinset.card ≤ 3 := by
          apply card_nodup_roots_le_three b
          simp only [Multiset.mem_toFinset] at hb
          exact isRoot_of_mem_roots hb
        apply le_trans (card_union_le _ _)
        have hcard : #(P - 1).roots.toFinset + #(P + 1).roots.toFinset ≤ 6 := by
          trans 3 + 3
          · gcongr
          · simp
        by_cases hP' : P.natDegree ≥ 4
        · -- therefore, if deg(P)≥ 4, we have n(P) ≤ 6 ≤ deg(P) + 2
          apply le_trans hcard
          exact Nat.sub_le_iff_le_add'.mp hP'
        · -- otherwise, we have deg(P) = 3
          -- assume that n(P)>deg(P) + 2, i.e., n(P)=6
          simp at hP'
          have hP : P.natDegree = 3 := by
            apply le_antisymm
            · exact Nat.le_of_lt_succ hP'
            · exact hP
          simp [hP]
          by_contra hcard_gt
          simp at hcard_gt
          -- (P-1) and P+1 have at most 3 roots, so they have exactly 3 roots each
          have hcard : (P - 1).roots.toFinset.card + (P + 1).roots.toFinset.card = 6 := by
            apply le_antisymm hcard
            exact hcard_gt
          have hcard₁ : (P - 1).roots.toFinset.card = 3 := by
            apply le_antisymm ha
            by_contra hcard₁
            simp at hcard₁
            have hcard' : (P - 1).roots.toFinset.card + (P + 1).roots.toFinset.card < 6 := by
              linarith only [hcard₁, hb]
            simp [hcard] at hcard'
          have hcard₂ : (P + 1).roots.toFinset.card = 3 := by
            simp [hcard₁] at hcard
            linarith only [hcard]
          -- However, by the lemma, we have that (P - 1)(x) = 0 has at most 2 roots when (P + 1)(x) = 0 has 3 roots, which contradicts the assumption
          apply card_nodup_roots_le_two at hcard₂
          simp [hcard₁] at hcard₂
