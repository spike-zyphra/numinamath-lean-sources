import Mathlib

lemma sum_fact_lt_fact_succ {n : ℕ} (n_le_3 : 3 ≤ n) :
    (Finset.range n).sum Nat.factorial < n.factorial := by
  refine Nat.le_induction ?base ?step n n_le_3
  case base =>
    repeat rw [Finset.sum_range_succ, Nat.factorial_succ]
    norm_num
  case step =>
    intro m m_ge_3 ih
    simp [Finset.range_succ]
    rw [Nat.factorial_succ, add_mul, one_mul, add_comm]
    gcongr
    suffices  ∑ x ∈ Finset.range m, x.factorial < m.factorial by
      have : 1 < m := by linarith
      have : m.factorial < m * m.factorial := by
        linear_combination this * m.factorial
      linarith
    exact ih

def fact_sums := Finset.image (Finset.sum · Nat.factorial)
  ∘ .powerset
  ∘ .range

def sums_card := Finset.card
  ∘ .filter (· ≠ 0)
  ∘ fact_sums

def fact_sums_rec
  | 0 => {0}
  | m + 1 => if m + 1 ≤ 3
    then Finset.image (Finset.sum · Nat.factorial)
      ∘ .powerset
      ∘ .range
      $ (m + 1)
    else fact_sums_rec (m) ∪ ((fact_sums_rec m).image (· + m.factorial))

lemma fact_gt : ∀ n ≥ 3, ∀ m ∈ fact_sums n, m < n.factorial := by
  intro n n_ge_3 m m_in
  have := sum_fact_lt_fact_succ n_ge_3
  rw [fact_sums] at m_in
  obtain ⟨ a, ⟨ a_in, a_sum ⟩ ⟩ := by
    simpa using m_in

  subst m
  have : a.sum Nat.factorial ≤ (Finset.range n).sum Nat.factorial := by
    exact Finset.sum_le_sum_of_ne_zero λ _ a _ => a_in a

  omega

lemma fact_sums_disjoint : ∀ n ≥ 3, Disjoint (fact_sums n)
  ((fact_sums n).image (· + (n).factorial))
    := by
  intro n n_ge_3
  simp [Disjoint]
  intro subset subset_in subset_image
  rw [@Finset.eq_empty_iff_forall_not_mem]
  intro m m_in
  have : ∀ x ∈ Finset.image (fun x ↦ x + n.factorial) (fact_sums n), n.factorial ≤ x := by
    simp
  have : n.factorial ≤ m := this m (subset_image m_in)
  have : m < n.factorial := fact_gt n n_ge_3 m (subset_in m_in)
  omega


lemma fact_sums_rec_eq {n} : fact_sums n = fact_sums_rec n := by
  induction' n using fact_sums_rec.induct with n n_lt_3 m m_ge_3 ih
  any_goals
    unfold fact_sums fact_sums_rec
    simp_all

  split_ifs
  · simp
  have h₁ : Finset.range (m + 1) = Finset.range m ∪ {m} := by
    ext
    simp [Finset.range_add_one, Or.comm]

  let p := (Finset.range m).powerset
  have h₂ : (Finset.range (m + 1)).powerset = p ∪ p.image λ s => s ∪ {m} := by
    aesop

  rw [h₂]
  rw [Finset.image_union]
  congr 1
  rw [<- ih]
  unfold fact_sums
  simp_all
  ext x
  simp_all
  simp_all only [Finset.mem_powerset, p]
  apply Iff.intro
  all_goals
    intro a
    obtain ⟨a, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    use a
    refine And.intro left ?_
    have disjoint : Disjoint a {m} := by
      suffices m ∉ a by simp_all
      intro m_in
      have := fact_gt m (by linarith)
      simp [fact_sums] at this
      specialize this a left
      have : {m} ⊆ a := by exact Finset.singleton_subset_iff.mpr m_in
      have : m  ∉ Finset.range m := by exact Finset.not_mem_range_self
      exact this (left m_in)

    have sum_comm : a.sum Nat.factorial + m.factorial = (a ∪ {m}).sum Nat.factorial := by
      simp [Finset.sum_union disjoint]

    simp [sum_comm]

lemma subset_union {s u v : Finset ℕ} : s ⊆ u → s ⊆ u ∪ v := by
  intro s_in
  rw [@Finset.subset_iff]
  intro x x_in
  exact Finset.mem_union_left v (s_in x_in)


lemma fact_sums_succ {n x} : x ∈ fact_sums n → x ∈ fact_sums (n + 1) := by
  intro x_in
  suffices fact_sums n ⊆ fact_sums (n + 1) by
    exact this x_in

  simp [fact_sums_rec_eq]
  conv_rhs => unfold fact_sums_rec
  simp [Function.comp_apply]
  split_ifs with n_ge_3
  · interval_cases n <;>
      exact Finset.inter_eq_right.mp rfl
  · exact subset_union fun ⦃a⦄ a ↦ a


lemma fact_sums_succ_eq_union {n} : fact_sums (n + 1)
  = fact_sums n ∪ (fact_sums n).image (· + (n).factorial)
    := by
  simp [fact_sums_rec_eq]
  conv_lhs => unfold fact_sums_rec
  split_ifs
  · interval_cases h : (n + 1) <;>
      aesop
  · rfl

lemma zero_in {n} : 0 ∈ fact_sums n := by
  simp [fact_sums, Function.comp_apply]
  use ∅
  simp

lemma sums_card_diff_0 : ∀ n, sums_card n = (fact_sums n).card - 1 := by
  intro n
  have card_no_0 : ((fact_sums n) \ {0}).card = (fact_sums n).card - 1 := by
    apply Finset.card_sdiff (by exact Finset.singleton_subset_iff.mpr zero_in)

  simp [sums_card]
  convert card_no_0 using 2
  ext a
  simp_all

lemma fact_sums_nonempty : ∀ n, fact_sums n ≠ ∅ := by
  intro n
  simp [fact_sums, Function.comp_apply]
  have : ∅ ∈ (Finset.range n).powerset := by
    simp
  exact Finset.ne_empty_of_mem this

lemma one_in : ∀ n > 0, 1 ∈ fact_sums n := by
  refine Nat.le_induction ?base ?step
  · simp [fact_sums]
  · intro m pos_m ih
    by_cases m_ge_3 : m ≤ 3
    · interval_cases m <;>
        apply Finset.insert_eq_self.mp
        rfl
    · push_neg at m_ge_3
      rw [fact_sums_succ_eq_union]
      exact Finset.mem_union_left
        (Finset.image (fun x ↦ x + m.factorial) (fact_sums m)) ih

lemma fact_sums_no_0 : ∀ n > 0, {x ∈ fact_sums n | ¬x = 0}.card =
    (fact_sums n).card - 1 := by
  intro n pos_n
  have disjoint : Disjoint {x ∈ fact_sums n | ¬x = 0} {0} := by
    aesop
  have : fact_sums n = {x ∈ fact_sums n | ¬x = 0} ∪ {0} := by
    convert_to fact_sums n = ( (fact_sums n) \ {0}) ∪ {0}
    · congr
      simp_all
      ext a
      simp_all
    · have := @zero_in n
      simp_all
  conv_rhs => rw [this]
  simp [Finset.card_union_of_disjoint disjoint]

lemma sums_card_pos : ∀ n > 0, 0 < sums_card n := by
  intro n pos_n
  unfold sums_card
  have : 1 ∈ fact_sums n := one_in n pos_n
  have : 1 ∈ {x ∈ fact_sums n | ¬x = 0} := by
    simp_all
  have : {x ∈ fact_sums n | ¬x = 0}.Nonempty := by
    use 1

  simp_all

lemma sums_card_succ : ∀ n ≥ 3, sums_card (n + 1) = 2 * (sums_card n) + 1 := by
  intro n n_ge_3
  rw [sums_card_diff_0]
  rw [fact_sums_succ_eq_union]
  simp [Finset.card_union_of_disjoint (fact_sums_disjoint n n_ge_3)]
  rw [Finset.card_image_of_injective _ (add_left_injective n.factorial)]
  rw [<- two_mul]
  suffices (fact_sums n).card = sums_card n + 1 by
    omega
  unfold sums_card
  simp_all
  rw [fact_sums_no_0]
  · suffices 0 < (fact_sums n).card by omega
    simp [fact_sums_nonempty]
    use 0
    exact zero_in
  · positivity

lemma sums_card_formula :
  ∀ n ≥ 3, sums_card n = 5 * 2^(n - 3) - 1 := by
  refine Nat.le_induction ?base ?step
  case base => rfl
  case step =>
    intro m m_ge_3 ih
    conv_rhs => calc 5 * 2 ^ (m + 1 - 3) - 1
      _ = 5 * 2 ^ (m - 3 + 1) - 1 := by
        rw [Nat.sub_add_comm m_ge_3]
      _ = 5 * (2 * 2 ^ (m - 3)) - 1 := by
        rw [@Nat.pow_add_one' 2 (m - 3)]
      _ = 2 * (5 * 2 ^ (m - 3)) - 1 := by ring_nf
      _ = 2 * (sums_card m + 1) - 1 := by
        have : 0 < 5 * 2 ^ (m - 3) := by
          positivity
        omega
      _ = 2 * (sums_card m) + 1 := by
        omega

    exact sums_card_succ m m_ge_3

theorem number_theory_608644 : sums_card 6 = 39 := by
  suffices sums_card 6 + 1 = 40 by linarith
  rw [sums_card_formula 6 (by simp)]
  rfl
