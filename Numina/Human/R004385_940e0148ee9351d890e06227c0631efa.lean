import Mathlib

open Real

/- Let $S$ be a finite set of positive real numbers. If $S$ 's average is at most 1 but its product is at least 0.9 , show that any three elements of $S$ can form the sides of a triangle. -/

--  am gm for multiset
lemma l_am_gm (S : Multiset ℝ) (hS : S.card ≠ 0) (h : ∀ x ∈ S, 0 < x) :
    (S.prod) ^ (1 / S.card : ℝ) ≤ S.sum / S.card := by
  rw [one_div]
  obtain ⟨S⟩ := S
  simp only [Multiset.quot_mk_to_coe'', Multiset.coe_card, ne_eq] at hS
  simp only [Multiset.quot_mk_to_coe'', Multiset.mem_coe] at h
  simp only [Multiset.quot_mk_to_coe'', Multiset.prod_coe, Multiset.coe_card, Multiset.sum_coe]
  have := Real.geom_mean_le_arith_mean Finset.univ (fun _ => 1) S.get (fun _ _ => by norm_num)
    (by simp; omega)
  simp only [Finset.mem_univ, List.get_eq_getElem, forall_const, rpow_one, Fin.prod_univ_get,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_mul,
    Fin.sum_univ_get] at this
  apply this
  rintro i
  exact (h S[i.val] (by apply List.getElem_mem)).le

-- for multiset if B is subset of A then (A - B).sum = A.sum - B.sum
lemma l_multiset_sum_sub {A B : Multiset ℝ} (h : B ≤ A) : (A - B).sum = A.sum - B.sum := by
  suffices (A - B).sum + B.sum = A.sum by linarith
  rw [← Multiset.sum_add, ← Multiset.union_def, Multiset.eq_union_left h]

-- for multiset if B is subset of A and 0 is not in B, then (A - B).prod = A.prod / B.prod
lemma l_multiset_prod_sub {A B : Multiset ℝ} (h : B ≤ A) (hB : 0 ∉ B) : (A - B).prod = A.prod / B.prod := by
  suffices (A - B).prod * B.prod = A.prod by
    have : B.prod ≠ 0 := by simpa
    field_simp
    assumption
  rw [← Multiset.prod_add, ← Multiset.union_def, Multiset.eq_union_left h]

-- if positive a, b, c have a + b ≤ c then a * b * c ≤ (a + b + c)^3  / 32
lemma l_ineq {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b ≤ c) :
    a * b * c ≤ (a + b + c)^3 / 32 := by
  let s := (a + b + c)
  trans (s - c)^2 / 4 * c
  -- a * b ≤ (s - c)^2 / 4 by normal algebra
  . gcongr
    linarith [sq_nonneg (a - b)]
  -- then (s - c)^2 * c ≤ s^3 / 8 as this is equivalent to 0 ≤ (2 * c  - s) * (4 * c * (s - c) + s * (2 * c - s)) which is true due to c ≤ s ≤ 2 * c
  . suffices (s - c)^2 * c ≤ s^3 / 8 by linarith
    have : 0 ≤ s - c := by
      convert_to 0 ≤ a + b + c - c
      linarith
    have : 0 ≤ 2 * c - s := by
      convert_to 0 ≤ 2 * c - (a + b + c)
      linarith
    suffices 0 ≤ (2 * c - s) * (4 * c * (s - c) + s * (2 * c - s)) by
      linear_combination this / 8
    positivity

theorem inequalities_259333 (S : Finset ℝ) (hS : ∀ x ∈ S, 0 < x) (hS_card : S.card ≠ 0)
    (hS1 : ∑ x ∈ S, x ≤ 1 * S.card) (hS2 : ∏ x ∈ S, x ≥ 0.9) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y ∧ y ≠ z ∧ z ≠ x →
    (x + y > z ∧ y + z > x ∧ z + x > y) := by
  -- assume not true, then there is a, b, c from set which do not form triangle
  by_contra h
  simp at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac, h⟩ := h
  replace h : a + b ≤ c ∨ b + c ≤ a ∨ c + a ≤ b := by
    revert h
    rw [show c < a + b ↔ ¬ (a + b ≤ c) by simp, show a < b + c ↔ ¬ (b + c ≤ a) by simp]
    tauto
  -- wlog a + b ≤ c as otherwise, other variations are witness for counter example
  wlog h' : a + b ≤ c generalizing a b c
  . simp [h'] at h
    obtain h | h := h
    . apply this b hb c hc a ha hbc hac hab (by simp [h]) h
    . apply this c hc a ha b hb hac hab hbc (by simp [h]) h
  clear h
  -- represent S as multiset, as rest of proof is easier that way
  obtain ⟨S⟩ := S
  simp at *
  let s := (a + b + c)/3
  -- consider following new multiset, we'll use this for contradiction
  let S' : Multiset ℝ := (S - {a, b, c}) + {s, s, s}
  replace hS_card : S.card ≠ 0 := by simpa
  -- {a, b, c} ≤ S, this will be used multiple times
  have h : {a, b, c} ≤ S := by
    simp
    refine (Multiset.cons_le_of_not_mem ?_).mpr ?_
    . rw [eq_comm] at hac; simp [hab, hac]
    . simp [ha]
      refine (Multiset.cons_le_of_not_mem ?_).mpr ?_
      . simp [hbc]
      . simp [hb, hc]
  -- new multiset has same cardinality and sum as old one
  have hS'_card : S'.card = S.card := by
    rw [Multiset.card_add, Multiset.card_sub h]
    simp
    have : 3 ≤ S.card := by convert Multiset.card_le_card h
    omega
  -- so in paritcular avrage is <= 1
  have hS1' : S'.sum / S'.card ≤ 1 := by
    rw [hS'_card, div_le_one (by norm_cast; omega)]
    convert hS1 using 1
    rw [Multiset.sum_add, l_multiset_sum_sub h]
    simp
    ring
  -- the product of new set is old product / (a * b * c) * s^3
  have hS2' : S'.prod = S.prod / (a * b * c) * s^3 := by
    rw [Multiset.prod_add, l_multiset_prod_sub h]
    . simp
      ring_nf
    . by_contra h'
      have := Multiset.mem_of_le h h'
      specialize hS 0 this
      norm_num at hS
  have ha' : 0 < a := hS a ha
  have hb' : 0 < b := hS b hb
  have hc' : 0 < c := hS c hc
  -- by lemma 32 / 27 ≤ s^3 / (a * b * c) and so product of new set is greater than 1
  replace hS2' : 1 < S'.prod := by
    rw [hS2', mul_comm_div]
    suffices 0.9 * (32 / 27) ≤ S.prod * (s^3 / (a * b * c)) by linarith
    gcongr ?_ * ?_
    rw [le_div_iff₀ (by positivity)]
    convert_to 32 / 27 * (a * b * c) ≤ ((a + b + c) / 3)^3
    have := l_ineq ha' hb' hc' h'
    linarith
  -- so geometric mean of new set is greater than 1
  replace hS2' := Real.one_lt_rpow hS2' (show 0 < 1 / (S'.card : ℝ) by simp; omega)
  -- all elements of new set is positive
  have hS' (x : ℝ) (h : x ∈ S') : 0 < x := by
    rw [Multiset.mem_add] at h
    obtain h | h := h
    . replace h := Multiset.mem_of_le (Multiset.sub_le_self _ _) h
      apply hS
      assumption
    . simp at h
      convert_to 0 < (a + b + c) / 3
      linarith
  -- hence the inequalities contradict am-gm
  have H := l_am_gm S' (by rwa [hS'_card]) hS'
  linarith