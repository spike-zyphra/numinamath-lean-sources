import Mathlib
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

lemma split_improves_prod (m : ℕ) (hm : 4 < m) : m < 2 * (m - 2) := by
  replace hm : 4 < m := hm
  contrapose! hm
  simp [Nat.mul_sub, add_comm m] at hm
  have : 2 * m - m ≤ 4 + m - m := by gcongr
  conv_rhs at this => simp
  simpa [two_mul] using this

lemma pos_prod (l : Multiset ℕ) (no_zero : 0 ∉ l)
  : 0 < l.prod := by
  suffices 0 ≠ l.prod by exact Nat.zero_lt_of_ne_zero this.symm
  symm
  intro prod_zero
  rw [Multiset.prod_eq_zero_iff] at prod_zero
  contradiction

lemma no_larger_than_4 (n) (l : List ℕ)
  (n_gt_4 : 4 < n) (no_zero : 0 ∉ l)
  : (n :: l).sum = (2 :: (n - 2) :: l).sum
  ∧ (n :: l).prod < (2 :: (n - 2) :: l).prod
    := by
  constructor
  ·
    simp [show (n :: l).sum = n + l.sum by rfl]
    omega
  ·
    have := split_improves_prod n n_gt_4
    rw [show (n :: l).prod = n * l.prod by rfl]
    simp [<- mul_assoc]
    gcongr
    exact pos_prod l no_zero


lemma best_list_le_4 : ∀ optimal : List ℕ, 0 ∉ optimal →
  (¬∃ candidate : List ℕ, candidate.sum = optimal.sum
    ∧ candidate.prod > optimal.prod)
  → ∀ n ∈ optimal, n ≤ 4 := by
  intro optimal no_zero not_exists n n_mem
  contrapose! not_exists with n_gt
  obtain ⟨ xs, ys, l_eq ⟩ := List.mem_iff_append.mp n_mem
  use 2 :: (n - 2) :: xs ++ ys
  rw [l_eq]
  have : 0 ∉ xs ++ ys := by subst l_eq; simp_all only [List.mem_append, List.mem_cons, not_or, true_or, or_true,
    or_self, not_false_eq_true]
  have := (no_larger_than_4 n ( xs ++ ys) n_gt this)
  simp
  simp at this
  convert this using 2
  · omega
  · omega
  · simp [<- mul_assoc, mul_comm]

lemma best_mset_le_4: ∀ optimal : Multiset ℕ, 0 ∉ optimal →
  (¬∃ candidate : Multiset ℕ, candidate.sum = optimal.sum
    ∧ candidate.prod > optimal.prod)
  → ∀ n ∈ optimal, n ≤ 4 := by
    intro optimal no_zero not_exists n n_mem
    rw [<- Multiset.coe_toList optimal] at *
    apply best_list_le_4 optimal.toList no_zero
      ?_ n n_mem
    simp
    intro candidate
    simp at not_exists
    specialize not_exists candidate
    exact not_exists


lemma two_2s_equal_4 (l : Multiset ℕ)
  : (insert 4 l).prod = (insert 2 (insert 2 l)).prod
  ∧ (insert 4 l).sum = (insert 2 (insert 2 l)).sum
    := by
  constructor
  · simp [<- mul_assoc]
  · simp [<- add_assoc]

lemma Multiset.add_sub_cancel {t s : Multiset ℕ} (hts : t ≤ s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

lemma mem_Ioc_succ {a b} : a ∈ Set.Ioc b (b + 1) → a = b + 1 := by
  intro mem
  simp at mem
  omega

lemma no_subset : ∀ optimal : Multiset ℕ, 0 ∉ optimal →
  (¬∃ candidate : Multiset ℕ, candidate.sum = optimal.sum
    ∧ candidate.prod > optimal.prod) →
  ¬{2, 2, 2} ≤ optimal ∧ ¬{2, 4} ≤ optimal ∧
  ¬{4, 4} ≤ optimal ∧ ¬{2, 2, 4} ≤ optimal
    := by
  rintro optimal no_zero not_exists
  simp only [<- not_or]
  rintro (s | s | s | s)
  all_goals contrapose! not_exists with gt

  use {3, 3} + (optimal - {2, 2, 2})
  rotate_left
  use {3, 3} + (optimal - {2, 4})
  rotate_left
  use {2, 3, 3} + (optimal - {4, 4})
  rotate_left
  use {2, 3, 3} + (optimal - {2, 2, 4})

  all_goals
  constructor
  · all_goals
    conv_rhs => rw [<- Multiset.add_sub_cancel s]
    simp only [Multiset.sum_add]
    conv_rhs => rw [add_comm]
    rfl

  · all_goals
    have : 0 < optimal.prod := by
      exact pos_prod optimal no_zero
    conv_rhs => rw [<- Multiset.add_sub_cancel s]
    simp only [Multiset.prod_add]
    conv_rhs => rw [mul_comm]
    gcongr
    · simp
      intro x x_in
      suffices x ≠ 0 from Nat.zero_lt_of_ne_zero this
      intro eq
      subst eq
      repeat
        apply Multiset.mem_of_mem_erase at x_in
        try contradiction
    · simp

lemma no_ones (n) (l : Multiset ℕ) (no_zero : 0 ∉ l)
  : (insert 1 (insert n l)).sum = (insert (n + 1) l).sum
  ∧ (insert 1 (insert n l)).prod < (insert (n + 1) l).prod
    := by
  constructor
  ·
    simp [<- mul_assoc]
    simp_all [<- add_assoc, add_comm]
  ·
    simp
    gcongr
    · simp
      intro x x_in
      suffices x ≠ 0 from Nat.zero_lt_of_ne_zero this
      intro x_eq
      subst x
      contradiction
    · exact lt_add_one n

lemma count_not_le (S : Multiset ℕ) (h : Multiset.count 2 S ≥ 3) : {2, 2, 2} ≤ S := by
  rw [Multiset.le_iff_count]
  intro n
  simp [Multiset.count_cons, Multiset.count_zero, Multiset.count_singleton]
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp; exact h
      | succ n => simp

lemma best_list_gt_1 : ∀ optimal : List ℕ, 0 ∉ optimal →
  optimal.sum = 2017 →
  (¬∃ candidate : List ℕ, candidate.sum = optimal.sum
    ∧ candidate.prod > optimal.prod)
  → ∀ n ∈ optimal, n > 1
    := by
  intro optimal no_zero _ not_exists n n_mem
  contrapose! not_exists with not_lt_of_gt
  replace n_gt : n = 1 := by
    by_contra! ne
    have : n = 0 := by omega
    subst n
    contradiction
  subst n_gt
  obtain ⟨ xs, ys, l_eq ⟩ := List.mem_iff_append.mp n_mem
  subst l_eq
  rw [show (xs ++ 1 :: ys).sum = (1 :: (xs ++ ys)).sum by
    simp only [List.sum_append, List.sum_cons, add_assoc, add_comm]
  ]
  rw [show (xs ++ 1 :: ys).prod = (xs ++ ys).prod by simp]
  cases h : (xs ++ ys)
  · simp_all
  · rename_i head tail
    have : 0 ∉ tail := by
      simp at no_zero
      have : 0 ∉ xs ++ ys := by
        simp [no_zero]
      rw [h] at this
      exact List.not_mem_of_not_mem_cons this

    have := no_ones head tail this
    simp [<- add_assoc] at this
    use (1 + head) :: tail
    simp
    constructor <;> linarith

lemma best_mset_gt_1 : ∀ optimal : Multiset ℕ,
  0 ∉ optimal → optimal.sum = 2017 →
  (¬∃ candidate : Multiset ℕ, candidate.sum = optimal.sum
    ∧ candidate.prod > optimal.prod)
  → ∀ n ∈ optimal, n > 1
    := by
    intro optimal no_zero sum_eq not_exists n n_mem
    rw [<- Multiset.coe_toList optimal] at *
    apply best_list_gt_1 optimal.toList no_zero
      sum_eq ?_ n n_mem

    simp
    intro candidate
    simp at not_exists
    specialize not_exists candidate
    exact not_exists


theorem homogeneous_list_prod_eq_pow (n base : ℕ) :
  (List.replicate n base).prod = base^n := by
  simp only [List.prod_replicate]


lemma best_subset : ∀ optimal : Multiset ℕ, 0 ∉ optimal →
  optimal.sum = 2017 →
  (¬∃ candidate : Multiset ℕ, candidate.sum = optimal.sum
    ∧ candidate.prod > optimal.prod
  ) → optimal ⊆ {2,3,4}
    := by
  intro optimal no_zero optimal_sum not_exists n n_mem
  have := best_mset_gt_1 optimal no_zero optimal_sum not_exists n n_mem
  have := best_mset_le_4 optimal no_zero not_exists n n_mem
  interval_cases n <;> simp

lemma diff_is_le {s t r: Multiset ℕ} : t ≤ s → r ≤ s - t →
  r + t ≤ s := by
  intro t_le_s r_le_diff
  exact (le_tsub_iff_right t_le_s).mp r_le_diff

lemma le_is_diff {s t r: Multiset ℕ} : t ≤ s → r + t ≤ s →
  r ≤ s - t
   := by
  intro t_le_s r_le_diff
  exact (le_tsub_iff_right t_le_s).mpr r_le_diff

lemma list_in_le {x: ℕ} {s t : Multiset ℕ} : t ≤ s → x ∈ s - t →
    x ::ₘ t ≤ s := by
  intro t_le_s x_in_diff
  suffices {x} + t ≤ s by simp_all only [Multiset.singleton_add]
  apply diff_is_le t_le_s (Multiset.singleton_le.mpr x_in_diff)

lemma count_not_in (x y : ℕ) (s : Multiset ℕ) :
  y ∈ s - Multiset.replicate (s.count x) x → y ≠ x
    := by
  intro y_in y_eq
  subst y_eq
  simp only [Multiset.mem_sub] at y_in
  simp_all only [Multiset.count_replicate_self, lt_self_iff_false]


lemma best_2_or_4 : ∀ optimal : Multiset ℕ, 0 ∉ optimal →
  (¬∃ candidate : Multiset ℕ, candidate.sum = optimal.sum
    ∧ candidate.prod > optimal.prod) →
  optimal.sum = 2017 →
    optimal = {2, 2} + Multiset.replicate 671 3 ∨
    optimal = {4} + Multiset.replicate 671 3
    := by
  intro optimal no_zero not_exists sum_eq
  have optimal_le : ¬{2, 2, 2} ≤ optimal ∧ ¬{2, 4} ≤ optimal ∧
    ¬{4, 4} ≤ optimal ∧ ¬{2, 2, 4} ≤ optimal :=
      no_subset optimal no_zero not_exists

  have optimal_subset : optimal ⊆ {2, 3, 4} :=
    best_subset optimal no_zero sum_eq not_exists

  have optimal_mem : ∀ x, x ∈ optimal → x ∈ ({2, 3, 4} : Multiset ℕ) := by
    exact fun x a ↦ optimal_subset a

  replace two_or_four : 2 ∈ optimal ∨ optimal ⊆ {3, 4} := by
    by_cases h : 2 ∈ optimal
    · exact Or.inl h
    · apply Or.inr
      have : ∀ ⦃x : ℕ⦄, x ∈ optimal → x ∈ ({3, 4} : Multiset ℕ) := by
        intro x x_in
        cases @optimal_mem x x_in
        · contradiction
        · rename_i x_mem
          simp
          exact List.mem_pair.mp x_mem

      rwa [<- Multiset.subset_iff] at this

  replace two_or_four : 2 ∈ optimal ∨ 4 ∈ optimal := by
    by_cases h : 2 ∈ optimal
    · exact Or.inl h
    · apply Or.inr
      by_cases g : 4 ∈ optimal
      · exact g
      rw [Multiset.pair_comm 3 4] at  two_or_four
      simp [h] at two_or_four
      have : ∀ x, x ∈ optimal → x ∈ ({4, 3} : Multiset ℕ) := by
        exact fun x a ↦ two_or_four a

      have : ∀ ⦃x : ℕ⦄, x ∈ optimal → x = 3 := by
        intro x x_in
        cases @this x x_in
        · contradiction
        · rename_i x_mem
          exact mem_Ioc_succ (Set.mem_toFinset.mp x_mem)

      have mul3 : (Multiset.replicate optimal.card 3).sum = optimal.card * 3 :=
        Multiset.sum_replicate optimal.card 3

      have : 3 ∣ optimal.sum := by
        rw [Multiset.eq_replicate_of_mem this]
        exact Dvd.intro_left optimal.card mul3.symm

      have : ¬3 ∣ optimal.sum := by
        rw [sum_eq]
        norm_num

      contradiction

  replace two_or_four :
    2 ∈ optimal ∧ 4 ∉ optimal ∨
    4 ∈ optimal ∧ 2 ∉ optimal := by
    by_cases h : 2 ∈ optimal ∧ 4 ∉ optimal
    · exact Or.inl h
    ·
      right
      rw [not_and_or] at h
      rcases h with (no_two | no_four)
      ·
        simp [no_two]
        cases two_or_four <;> simp_all
      ·
        have : ¬(2 ∈ optimal ∧ 4 ∈ optimal) := by
          rintro ⟨ two_in, four_in ⟩
          have two_in : {2} ≤ optimal := by
            exact Multiset.singleton_le.mpr two_in
          have : {4} ≤ optimal := by
            exact Multiset.singleton_le.mpr four_in
          have : ({2} : Multiset ℕ) + {4} ≤ optimal := by
            refine (Multiset.le_iff_subset ?_).mpr ?_
              <;> simp_all

          exact optimal_le.right.left this

        simp_all

  have two_no_four : 2 ∈ optimal ∧ 4 ∉ optimal →
    {2, 2} + Multiset.replicate 671 3 = optimal := by
    intro ⟨ two_in, no_four ⟩
    have two_le : {2} ≤ optimal := by
      simp_all

    replace optimal_subset : optimal ⊆ {2,3} := by
      have : 4 ∉ optimal.toFinset := by
        simpa [Multiset.mem_toFinset] using no_four
      have := optimal.toFinset.subset_insert_iff_of_not_mem this (t := {2,3})

      suffices optimal.toFinset ⊆ {2,3} by
        exact Multiset.dedup_subset'.mp this

      rw [<- this]
      have : optimal.toFinset ⊆ ({2,3,4} : Multiset ℕ).toFinset := by
        exact Multiset.toFinset_subset.mpr optimal_subset
      convert this
      decide

    have two_2s : optimal.count 2 = 2 := by
      have : optimal.count 2 < 3 := by
        by_contra! le
        have := Multiset.le_count_iff_replicate_le.mp le
        simp_all

      have : optimal.count 2 ≠ 1 := by
        by_contra!

        have fa_diff : ∀ ⦃x : ℕ⦄, x ∈ optimal - {2} → x = 3 := by
          intro x x_in
          simp at x_in
          have := count_not_in 2 x optimal
          have : x ≠ 2 := by
            simp_all only [gt_iff_lt, _root_.not_exists, not_and, not_lt, Multiset.insert_eq_cons, not_false_eq_true,
              and_self, not_true_eq_false, or_false, Multiset.singleton_le, Nat.one_lt_ofNat, Multiset.replicate_succ,
              Multiset.replicate_zero, Multiset.cons_zero, Multiset.sub_singleton, ne_eq, forall_const]
          have : x ∈ optimal := by
            exact Multiset.mem_of_mem_erase x_in

          cases optimal_subset this
          any_goals contradiction
          exact mem_Ioc_succ (Set.mem_toFinset.mp (by assumption))

        have disjoint : Disjoint (optimal - {2}) ({2} : Multiset ℕ) := by
          apply Multiset.disjoint_iff_ne.mpr
          intro x x_in_diff y y_in2 x_eq_y
          specialize fa_diff x_in_diff
          subst y x
          contradiction

        have rep_eq := Multiset.eq_replicate_of_mem fa_diff
        have sum_rep_eq : (optimal - {2}).sum = (Multiset.replicate (optimal - {2}).card 3).sum := by
          exact congrArg Multiset.sum rep_eq

        have sum_distrib : optimal.sum - ({2}:Multiset ℕ).sum = (optimal - {2}).sum := by
          rw [<- Multiset.add_sub_cancel two_le]
          simp

        have : optimal.sum - ({2} : Multiset ℕ).sum = 2015 := by
          rw [<- sum_distrib] at sum_rep_eq
          apply congrFun (congrArg HSub.hSub sum_eq) 2

        have card_distrib := Multiset.card_sub two_le

        have : (Multiset.replicate (optimal.card - 1) 3).sum = 2015 := by
          rw [<- this, sum_distrib, rep_eq]
          rw [card_distrib]
          rfl

        have mul3 : (Multiset.replicate (optimal.card - 1) 3).sum = (optimal.card - 1) * 3 :=
          Multiset.sum_replicate (optimal.card - 1) 3

        have : 3 * (optimal.card - 1) = 2015 := by
          omega

        omega

      have two_2s : optimal.count 2 ≠ 0 := by
        simp_all only [gt_iff_lt, _root_.not_exists, not_and, not_lt, Multiset.insert_eq_cons, not_false_eq_true,
          and_self, not_true_eq_false, or_false, Multiset.singleton_le, ne_eq, Multiset.count_eq_zero]

      omega

    have two_le : {2, 2} ≤ optimal := by
      rw [show {2, 2} = Multiset.replicate 2 2 by rfl]
      rw [<- Multiset.le_count_iff_replicate_le]
      simp [two_2s]


    have fa_ne_2 : ∀ x ∈ optimal - {2, 2}, x ≠ 2 := by
      intro x x_in
      have := count_not_in 2 x optimal
      rw [two_2s] at this
      exact this x_in

    replace fa_ne_2 : ∀ x ∈ optimal - {2, 2}, x = 3 := by
      intro x x_in
      specialize fa_ne_2 x x_in
      have : x ∈ optimal := by
        simp at x_in
        have := Multiset.mem_of_mem_erase x_in
        exact Multiset.mem_of_mem_erase this

      have optimal_mem : x ∈ optimal → x ∈ ({2,3} : Multiset ℕ) := by
        exact fun a ↦ optimal_subset this

      simp_all only [gt_iff_lt, _root_.not_exists, not_and, not_lt, Multiset.insert_eq_cons,
        Multiset.mem_cons, Multiset.mem_singleton, not_false_eq_true, and_self, not_true_eq_false,
        or_false, Multiset.singleton_le, Multiset.sub_cons, Multiset.sub_singleton, ne_eq, false_or,
        forall_const]

    rw [<- Multiset.eq_replicate_card] at fa_ne_2
    symm
    have : optimal - {2, 2} + {2, 2} = Multiset.replicate (optimal - {2, 2}).card 3 + {2, 2} := by
      exact congrFun (congrArg HAdd.hAdd fa_ne_2) {2, 2}
    rw [Multiset.add_sub_cancel two_le, add_comm] at this
    convert this using 2

    have sum_rep_eq : (optimal - {2, 2}).sum = (Multiset.replicate (optimal - {2, 2}).card 3).sum := by
      exact congrArg Multiset.sum fa_ne_2

    have summ_distrib : optimal.sum - ({2, 2}:Multiset ℕ).sum = (optimal - {2, 2}).sum := by
      rw [<- Multiset.add_sub_cancel two_le]
      norm_num [add_comm, <- add_assoc]

    have : optimal.sum - ({2, 2} : Multiset ℕ).sum = 2013 := by
      rw [<- summ_distrib] at sum_rep_eq
      apply congrFun (congrArg HSub.hSub sum_eq) 4

    have sum3s : (Multiset.replicate 671 3).sum = 671 * 3 := by
      rw [Multiset.sum_replicate]
      rfl

    have : (Multiset.replicate (optimal - {2, 2}).card 3).sum = 671 * 3 := by
      omega
    rw [Multiset.sum_replicate] at this
    have : (optimal - {2, 2}).card * 3 = 671 * 3 := by
      exact this
    have : (optimal - {2, 2}).card = 671 := by
      omega
    rw [this]


  have four_no_two : 4 ∈ optimal ∧ 2 ∉ optimal →
    {4} + Multiset.replicate 671 3 = optimal := by
    intro ⟨ four_in, no_two ⟩
    have two_le : {4} ≤ optimal := by
      simp_all

    replace optimal_subset : optimal ⊆ {4,3} := by
      have : 2 ∉ optimal.toFinset := by
        simpa [Multiset.mem_toFinset] using no_two
      have := optimal.toFinset.subset_insert_iff_of_not_mem this (t := {4,3})

      suffices optimal.toFinset ⊆ {4,3} by
        exact Multiset.dedup_subset'.mp this

      rw [<- this]
      have : optimal.toFinset ⊆ ({2,3,4} : Multiset ℕ).toFinset := by
        exact Multiset.toFinset_subset.mpr optimal_subset
      convert this
      decide

    have one_4s : optimal.count 4 = 1 := by
      have : optimal.count 4 < 2 := by
        by_contra! le
        have := Multiset.le_count_iff_replicate_le.mp le
        simp_all
      have : 0 < optimal.count 4 := by
        exact Multiset.count_pos.mpr four_in

      omega

    have two_le : {4} ≤ optimal := by
      rw [show {4} = Multiset.replicate 1 4 by rfl]
      rw [<- Multiset.le_count_iff_replicate_le]
      simp [one_4s]


    have fa_ne_4 : ∀ x ∈ optimal - {4}, x ≠ 4 := by
      intro x x_in
      have := count_not_in 4 x optimal
      rw [one_4s] at this
      exact this x_in

    replace fa_ne_2 : ∀ x ∈ optimal - {4}, x = 3 := by
      intro x x_in
      specialize fa_ne_4 x x_in
      have : x ∈ optimal := by
        simp at x_in
        exact Multiset.mem_of_mem_erase x_in

      have optimal_mem : x ∈ optimal → x ∈ ({4,3} : Multiset ℕ) := by
        exact fun a ↦ optimal_subset this

      simp_all only [gt_iff_lt, _root_.not_exists, not_and, not_lt, Multiset.insert_eq_cons,
        Multiset.mem_cons, Multiset.mem_singleton, not_false_eq_true, and_self, not_true_eq_false,
        or_false, Multiset.singleton_le, Multiset.sub_cons, Multiset.sub_singleton, ne_eq, false_or,
        forall_const]

    rw [<- Multiset.eq_replicate_card] at fa_ne_2
    symm
    have : optimal - {4} + {4} = Multiset.replicate (optimal - {4}).card 3 + {4} := by
      exact congrFun (congrArg HAdd.hAdd fa_ne_2) {4}
    rw [Multiset.add_sub_cancel two_le, add_comm] at this
    convert this using 2

    have sum_rep_eq : (optimal - {4}).sum = (Multiset.replicate (optimal - {4}).card 3).sum := by
      exact congrArg Multiset.sum fa_ne_2

    have summ_distrib : optimal.sum - ({4}:Multiset ℕ).sum = (optimal - {4}).sum := by
      rw [<- Multiset.add_sub_cancel two_le]
      norm_num [add_comm, <- add_assoc]

    have : optimal.sum - ({4} : Multiset ℕ).sum = 2013 := by
      rw [<- summ_distrib] at sum_rep_eq
      apply congrFun (congrArg HSub.hSub sum_eq) 4

    have sum3s : (Multiset.replicate 671 3).sum = 671 * 3 := by
      rw [Multiset.sum_replicate]
      rfl

    have : (Multiset.replicate (optimal - {4}).card 3).sum = 671 * 3 := by
      omega
    rw [Multiset.sum_replicate] at this
    have : (optimal - {4}).card * 3 = 671 * 3 := by
      exact this
    have : (optimal - {4}).card = 671 := by
      omega
    rw [this]

  rcases two_or_four with (h | g)
  · left
    rw [two_no_four h]
  · right
    rw [four_no_two g]


theorem number_theory_315382 :
  ∀ optimal : Multiset ℕ, 0 ∉ optimal →
  optimal.sum = 2017 →
  (¬∃ candidate : Multiset ℕ, candidate.sum = optimal.sum ∧
    candidate.prod > optimal.prod
  ) → optimal.prod = 2^2 * 3^671
    := by
  intro optimal no_zero optimal_sum candidate
  cases best_2_or_4 optimal no_zero candidate optimal_sum
  all_goals
    subst optimal
    rw [<- Multiset.prod_replicate 671]
    rw [Multiset.prod_add]
    congr
