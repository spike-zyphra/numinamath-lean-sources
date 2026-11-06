import Mathlib

def median (s : Finset ℕ) (card_five : s.card = 5) : ℕ :=
(@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ s).tail.tail.head (by
  intro tail_tail_nil
  rw [←@Finset.length_sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ s] at card_five
  rw [←@List.cons_head!_tail ℕ _ (@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ s) (by
    intro s_nil
    rw [s_nil] at card_five
    contradiction
  ), List.length_cons] at card_five
  rw [←@List.cons_head!_tail ℕ _ (@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ s).tail (by
    intro s_nil
    rw [s_nil] at card_five
    contradiction
  ), List.length_cons, tail_tail_nil] at card_five
  contradiction
)

def mean (s : Finset ℕ) : ℚ := (∑ x ∈ s, x) / s.card

/-
The set {3,6,9,10} is augmented by a fifth element n, not equal to any of the other four.
The median of the resulting set is equal to its mean. What is the sum of all possible values of n?
-/
theorem AMC_Algebra_1179 (t : Finset ℕ) -- t is the set of all possible values of n
  (mem_t : ∀ n : ℕ, n ∈ t ↔ Finset.card {n, 3, 6, 9, 10} = 5 ∧
    ∀ (card_five : Finset.card {n, 3, 6, 9, 10} = 5), median {n, 3, 6, 9, 10} card_five = mean {n, 3, 6, 9, 10}
  ) :
  ∑ x ∈ t, x = 26
  := by
/-
The median must either be 6, 9, or n.
-/
suffices med_eq : ∀ n ∈ t, ∀ (card_five : Finset.card {n, 3, 6, 9, 10} = 5), median {n, 3, 6, 9, 10} card_five ∈ ({6, 9, n} : Finset ℕ)
{
  /-
  Median is 6: Then n ≤ 6 and (3 + 6 + 9 + 10 + n)/5 = 6 ⟹ n = 2
  -/
  suffices n_eq_two_of_med_six : ∀ n ∈ t, ∀ (card_five : Finset.card {n, 3, 6, 9, 10} = 5), median {n, 3, 6, 9, 10} card_five = 6 → n = 2
  {
    /-
    Median is 9: Then n ≥ 9 and (3 + 6 + 9 + 10 + n)/5 = 9 ⟹ n = 17
    -/
    suffices n_eq_seventeen_of_med_nine : ∀ n ∈ t, ∀ (card_five : Finset.card {n, 3, 6, 9, 10} = 5), median {n, 3, 6, 9, 10} card_five = 9 → n = 17
    {
      /-
      Median is n: Then 6 ≤ n ≤ 9 and (3 + 6 + 9 + 10 + n)/5 = n ⟹ n = 7
      -/
      suffices n_eq_seven_of_med_n : ∀ n ∈ t, ∀ (card_five : Finset.card {n, 3, 6, 9, 10} = 5), median {n, 3, 6, 9, 10} card_five = n → n = 7
      {
        /-
        All three cases are valid, so our solution is 2 + 7 + 17 = 26 ⟹ (E).
        -/
        suffices t_eq : t = {2, 7, 17}
        {
          rw [t_eq]
          simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
            not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Nat.reduceAdd]
        }
        {
          ext
          rename_i n
          apply Iff.intro
          {
            intro n_in_t
            simp only [Finset.mem_insert, Finset.mem_singleton] at med_eq
            cases med_eq n n_in_t ((mem_t n).1 n_in_t).left
            {
              rename_i med_six
              rw [n_eq_two_of_med_six n n_in_t ((mem_t n).1 n_in_t).left med_six]
              simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                or_false]
            }
            rename_i med_eq
            cases med_eq
            {
              rename_i med_nine
              rw [n_eq_seventeen_of_med_nine n n_in_t ((mem_t n).1 n_in_t).left med_nine]
              simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_true]
            }
            {
              rename_i med_n
              rw [n_eq_seven_of_med_n n n_in_t ((mem_t n).1 n_in_t).left med_n]
              simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_false,
                or_true]
            }
          }
          {
            intro n_eq
            apply (mem_t n).2
            simp only [median, mean]
            simp only [Finset.mem_insert, Finset.mem_singleton] at n_eq
            cases n_eq
            {
              rename_i n_eq_two
              rw [n_eq_two]
              simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
                Nat.reduceAdd, List.head_tail, List.getElem_tail, Finset.sum_insert,
                Finset.sum_singleton, Nat.cast_ofNat, forall_true_left, true_and]
              norm_num
              apply Rat.natCast_inj.2
              simp only [@Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                2 {3, 6, 9, 10} (by
                  simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                    Nat.reduceLeDiff, forall_eq, and_self]
                ) (by
                  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                    not_false_eq_true]
                ), List.getElem_cons_succ]
              simp only [@Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                3 {6, 9, 10} (by
                  simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                    Nat.reduceLeDiff, forall_eq, and_self]
                ) (by
                  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                    not_false_eq_true]
                ), List.getElem_cons_succ]
              simp only [@Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                6 {9, 10} (by
                  simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                    Nat.reduceLeDiff, forall_eq, and_self]
                ) (by
                  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                    not_false_eq_true]
                ), List.getElem_cons_zero]
            }
            rename_i n_eq
            cases n_eq
            {
              rename_i n_eq_seven
              rw [n_eq_seven]
              simp only [Finset.mem_insert, Nat.reduceEqDiff, Nat.succ_ne_self,
                Finset.mem_singleton, or_self, not_false_eq_true, Finset.card_insert_of_not_mem,
                Finset.card_singleton, Nat.reduceAdd, List.head_tail, List.getElem_tail,
                Finset.sum_insert, Finset.sum_singleton, Nat.cast_ofNat, forall_true_left, true_and]
              norm_num
              apply Rat.natCast_inj.2
              suffices s_eq : ({7, 3, 6, 9, 10} : Finset ℕ) = {3, 6, 7, 9, 10}
              {
                simp only [s_eq, @Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                  3 {6, 7, 9, 10} (by
                    simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                      Nat.reduceLeDiff, forall_eq, and_self]
                  ) (by
                    simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                      not_false_eq_true]
                  ), List.getElem_cons_succ]
                simp only [@Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                  6 {7, 9, 10} (by
                    simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                      Nat.reduceLeDiff, forall_eq, and_self]
                  ) (by
                    simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                      not_false_eq_true]
                  ), List.getElem_cons_succ]
                simp only [@Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                  7 {9, 10} (by
                    simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                      Nat.reduceLeDiff, forall_eq, and_self]
                  ) (by
                    simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                      not_false_eq_true]
                  ), List.getElem_cons_zero]
              }
              {
                ext
                rename_i a
                simp only [Finset.mem_insert, Finset.mem_singleton]
                apply Iff.intro
                {
                  intro h
                  cases h
                  {
                    rename_i a_eq_seven
                    exact Or.inr (Or.inr (Or.inl a_eq_seven))
                  }
                  rename_i h
                  cases h
                  {
                    apply Or.inl
                    assumption
                  }
                  rename_i h
                  cases h
                  {
                    rename_i a_eq_six
                    exact Or.inr (Or.inl a_eq_six)
                  }
                  {
                    rename_i h
                    exact Or.inr (Or.inr (Or.inr h))
                  }
                }
                {
                  intro h
                  cases h
                  {
                    rename_i a_eq_three
                    exact Or.inr (Or.inl a_eq_three)
                  }
                  rename_i h
                  cases h
                  {
                    rename_i a_eq_six
                    exact Or.inr (Or.inr (Or.inl a_eq_six))
                  }
                  rename_i h
                  cases h
                  {
                    apply Or.inl
                    assumption
                  }
                  {
                    rename_i h
                    exact Or.inr (Or.inr (Or.inr h))
                  }
                }
              }
            }
            {
              rename_i n_eq_seventeen
              rw [n_eq_seventeen]
              simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
                Nat.reduceAdd, List.head_tail, List.getElem_tail, Finset.sum_insert,
                Finset.sum_singleton, Nat.cast_ofNat, forall_true_left, true_and]
              norm_num
              apply Rat.natCast_inj.2
              suffices s_eq : ({17, 3, 6, 9, 10} : Finset ℕ) = {3, 6, 9, 10, 17}
              {
                simp only [s_eq, @Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                  3 {6, 9, 10, 17} (by
                    simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                      Nat.reduceLeDiff, forall_eq, and_self]
                  ) (by
                    simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                      not_false_eq_true]
                  ), List.getElem_cons_succ]
                simp only [s_eq, @Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                  6 {9, 10, 17} (by
                    simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                      Nat.reduceLeDiff, forall_eq, and_self]
                  ) (by
                    simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                      not_false_eq_true]
                  ), List.getElem_cons_succ]
                simp only [s_eq, @Finset.sort_insert  ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _
                  9 {10, 17} (by
                    simp only [Finset.mem_insert, Finset.mem_singleton, Nat.le_eq, forall_eq_or_imp,
                      Nat.reduceLeDiff, forall_eq, and_self]
                  ) (by
                    simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                      not_false_eq_true]
                  ), List.getElem_cons_zero]
              }
              {
                ext
                rename_i a
                simp only [Finset.mem_insert, Finset.mem_singleton]
                apply Iff.intro
                {
                  intro h
                  cases h
                  {
                    rename_i a_eq_seventeen
                    exact Or.inr (Or.inr (Or.inr (Or.inr a_eq_seventeen)))
                  }
                  rename_i h
                  cases h
                  {
                    rename_i a_eq_three
                    exact Or.inl a_eq_three
                  }
                  rename_i h
                  cases h
                  {
                    rename_i a_eq_six
                    exact Or.inr (Or.inl a_eq_six)
                  }
                  rename_i h
                  cases h
                  {
                    rename_i a_eq_nine
                    exact Or.inr (Or.inr (Or.inl a_eq_nine))
                  }
                  {
                    rename_i a_eq_ten
                    exact Or.inr (Or.inr (Or.inr (Or.inl a_eq_ten)))
                  }
                }
                {
                  intro h
                  cases h
                  {
                    rename_i a_eq_three
                    exact Or.inr (Or.inl a_eq_three)
                  }
                  rename_i h
                  cases h
                  {
                    rename_i a_eq_six
                    exact Or.inr (Or.inr (Or.inl a_eq_six))
                  }
                  rename_i h
                  cases h
                  {
                    rename_i a_eq_nine
                    exact Or.inr (Or.inr (Or.inr (Or.inl a_eq_nine)))
                  }
                  rename_i h
                  cases h
                  {
                    rename_i a_eq_ten
                    exact Or.inr (Or.inr (Or.inr (Or.inr a_eq_ten)))
                  }
                  {
                    rename_i a_eq_seventeen
                    exact Or.inl a_eq_seventeen
                  }
                }
              }
            }
          }
        }
      }
      {
        intro n n_in_t _ med_n
        cases (mem_t n).1 n_in_t
        rename_i card_five med_eq_mean_of_card_five
        suffices med_eq_mean : ↑(median {n, 3, 6, 9, 10} card_five) = mean {n, 3, 6, 9, 10}
        {
          simp only [med_n, mean] at med_eq_mean
          rw [card_five] at med_eq_mean
          rw [Finset.sum_insert] at med_eq_mean
          {
            simp only [Nat.cast_ofNat, Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton,
              or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Nat.reduceAdd,
              Nat.cast_add] at med_eq_mean
            suffices med_mul_five_eq_mean_mul_five : (↑n : ℚ) * 5 = (↑n + 28) / 5 * 5
            {
              simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                IsUnit.div_mul_cancel] at med_mul_five_eq_mean_mul_five
              apply @Nat.mul_right_cancel n 4
              {norm_num}
              {
                apply @Nat.add_left_cancel n (n * 4)
                rw [Nat.add_comm, ←Nat.mul_add_one]
                apply Rat.natCast_inj.1
                simp only [Nat.reduceAdd, Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul, Nat.cast_add]
                assumption
              }
            }
            {rw [←med_eq_mean]}
          }
          {
            intro n_eq
            rw [Finset.card_insert_of_mem n_eq] at card_five
            simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
              not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
              Nat.reduceAdd] at card_five
          }
        }
        {
          apply med_eq_mean_of_card_five
        }
      }
    }
    {
      intro n n_in_t _ med_nine
      cases (mem_t n).1 n_in_t
      rename_i card_five med_eq_mean_of_card_five
      suffices med_eq_mean : ↑(median {n, 3, 6, 9, 10} card_five) = mean {n, 3, 6, 9, 10}
      {
        simp only [med_nine, mean] at med_eq_mean
        rw [card_five] at med_eq_mean
        rw [Finset.sum_insert] at med_eq_mean
        {
          simp only [Nat.cast_ofNat, Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton,
            or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Nat.reduceAdd,
            Nat.cast_add] at med_eq_mean
          suffices med_mul_five_eq_mean_mul_five : (9 : ℚ) * 5 = (↑n + 28) / 5 * 5
          {
            simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              IsUnit.div_mul_cancel] at med_mul_five_eq_mean_mul_five
            norm_num at med_mul_five_eq_mean_mul_five
            apply Eq.symm
            apply Rat.natCast_inj.1
            apply @AddRightCancelSemigroup.add_right_cancel ℚ _ ↑17 28 ↑n
            apply @Eq.trans ℚ (17 + 28) 45
            {norm_num}
            {assumption}
          }
          {rw [med_eq_mean]}
        }
        {
          intro n_eq
          rw [Finset.card_insert_of_mem n_eq] at card_five
          simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
            not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
            Nat.reduceAdd] at card_five
        }
      }
      {
        apply med_eq_mean_of_card_five
      }
    }
  }
  {
    intro n n_in_t _ med_six
    cases (mem_t n).1 n_in_t
    rename_i card_five med_eq_mean_of_card_five
    suffices med_eq_mean : ↑(median {n, 3, 6, 9, 10} card_five) = mean {n, 3, 6, 9, 10}
    {
      simp only [med_six, mean] at med_eq_mean
      rw [card_five] at med_eq_mean
      rw [Finset.sum_insert] at med_eq_mean
      {
        simp only [Nat.cast_ofNat, Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton,
          or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Nat.reduceAdd,
          Nat.cast_add] at med_eq_mean
        suffices med_mul_five_eq_mean_mul_five : (6 : ℚ) * 5 = (↑n + 28) / 5 * 5
        {
          simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            IsUnit.div_mul_cancel] at med_mul_five_eq_mean_mul_five
          norm_num at med_mul_five_eq_mean_mul_five
          apply Eq.symm
          apply Rat.natCast_inj.1
          apply @AddRightCancelSemigroup.add_right_cancel ℚ _ ↑2 28 ↑n
          apply @Eq.trans ℚ (2 + 28) 30
          {norm_num}
          {assumption}
        }
        {rw [med_eq_mean]}
      }
      {
        intro n_eq
        rw [Finset.card_insert_of_mem n_eq] at card_five
        simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
          not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
          Nat.reduceAdd] at card_five
      }
    }
    {
      apply med_eq_mean_of_card_five
    }
  }
}
{
  intro n n_in_t _
  cases (mem_t n).1 n_in_t
  rename_i card_five med_eq_mean_of_card_five
  suffices n_neq : n ∉ ({3, 6, 9, 10} : Finset ℕ)
  {
    suffices med_in_s : median {n, 3, 6, 9, 10} card_five ∈ ({n, 3, 6, 9, 10} : Finset ℕ)
    {
      simp only [Finset.mem_insert, Finset.mem_singleton] at med_in_s ⊢
      cases med_in_s
      {
        apply Or.inr
        apply Or.inr
        assumption
      }
      rename_i h
      cases h
      {
        rename_i med_three
        rw [median] at med_three
        simp only [List.head_tail, List.getElem_tail, Nat.reduceAdd] at med_three
        cases Nat.lt_or_ge n 3
        {
          rename_i n_lt_3
          suffices s_eq_cons : (@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 3, 6, 9, 10})
            = (@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ (Finset.cons n {3, 6, 9, 10} n_neq))
          {
            simp only [s_eq_cons, @Finset.sort_cons ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ n {3, 6, 9, 10} (by
              intro b b_mem
              simp only [Finset.mem_insert, Finset.mem_singleton] at b_mem
              cases b_mem
              {
                rename_i b_eq
                rw [b_eq]
                exact Nat.le_of_lt n_lt_3
              }
              rename_i b_mem
              cases b_mem
              {
                rename_i b_eq
                rw [b_eq]
                apply Nat.le_trans (Nat.le_of_lt n_lt_3)
                norm_num
              }
              rename_i b_mem
              cases b_mem
              {
                rename_i b_eq
                rw [b_eq]
                apply Nat.le_trans (Nat.le_of_lt n_lt_3)
                norm_num
              }
              {
                rename_i b_eq
                rw [b_eq]
                apply Nat.le_trans (Nat.le_of_lt n_lt_3)
                norm_num
              }
            ) n_neq, List.getElem_cons_succ] at med_three
            simp only [@Finset.sort_insert ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ _ 3 {6, 9, 10}
              (by
                intro b b_mem
                simp only [Finset.mem_insert, Finset.mem_singleton] at b_mem
                cases b_mem
                {
                  rename_i b_eq
                  rw [b_eq]
                  norm_num
                }
                rename_i b_mem
                cases b_mem
                repeat {
                  rename_i b_eq
                  rw [b_eq]
                  norm_num
                }
              ) (by simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                  not_false_eq_true]),
              List.getElem_cons_succ] at med_three
            suffices three_in_sort : 3 ∈ @Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {6, 9, 10}
            {
              suffices three_in_unsorted : 3 ∈ ({6, 9, 10} : Finset ℕ)
              {contradiction}
              {
                apply (@Finset.mem_sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {6, 9, 10} 3).1
                assumption
              }
            }
            {
              apply (@List.mem_iff_getElem ℕ 3
                (@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {6, 9, 10})).2
              apply Exists.intro 0
              apply Exists.intro (by simp only [Finset.length_sort, Finset.mem_insert,
                Nat.reduceEqDiff, Finset.mem_singleton, or_self, not_false_eq_true,
                Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, Nat.ofNat_pos])
              assumption
            }
          }
          {
            simp only [Finset.cons_eq_insert]
          }
        }
        {
          rename_i n_ge_three
          suffices s_eq : ({n, 3, 6, 9, 10} : Finset ℕ) = {3, n, 6, 9, 10}
          {
            simp only [s_eq] at med_three
            suffices s_sort_insert : @Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {3, n, 6, 9, 10}
              = 3 :: @Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 6, 9, 10}
            {
              simp only [s_sort_insert, List.getElem_cons_succ] at med_three
              suffices three_in_sort : 3 ∈ @Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 6, 9, 10}
              {
                suffices three_in_unsorted : 3 ∈ ({n, 6, 9, 10} : Finset ℕ)
                {
                  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                    or_false] at three_in_unsorted
                  rw [←three_in_unsorted] at n_neq
                  contradiction
                }
                {
                  apply (@Finset.mem_sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 6, 9, 10} 3).1
                  assumption
                }
              }
              {
                apply (@List.mem_iff_getElem ℕ 3
                  (@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 6, 9, 10})).2
                apply Exists.intro 1
                apply Exists.intro (by
                  simp only [Finset.length_sort]
                  rw [@Finset.card_insert_of_not_mem ℕ {6, 9, 10} n _ (by
                    intro n_mem
                    apply n_neq
                    simp only [Finset.mem_insert, Finset.mem_singleton] at n_mem ⊢
                    apply Or.inr
                    assumption
                  )]
                  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                    not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
                    Nat.reduceAdd, Nat.one_lt_ofNat]
                )
                assumption
              }
            }
            {
              apply @Finset.sort_insert ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩
              {
                intro b b_mem
                simp only [Finset.mem_insert, Finset.mem_singleton] at b_mem
                cases b_mem
                {
                  rename_i b_eq
                  rw [b_eq]
                  assumption
                }
                rename_i b_mem
                cases b_mem
                {
                  rename_i b_eq
                  rw [b_eq]
                  norm_num
                }
                rename_i b_mem
                cases b_mem
                repeat {
                  rename_i b_eq
                  rw [b_eq]
                  norm_num
                }
              }
              {
                simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                  or_false]
                intro three_eq_n
                rw [←three_eq_n] at n_neq
                contradiction
              }
            }
          }
          {
            ext
            rename_i a
            simp only [Finset.mem_insert, Finset.mem_singleton]
            apply Iff.intro
            {
              intro h
              cases h
              {
                rename_i a_eq_n
                exact Or.inr (Or.inl a_eq_n)
              }
              rename_i h
              cases h
              {
                rename_i a_eq_three
                exact Or.inl a_eq_three
              }
              {
                rename_i h
                exact Or.inr (Or.inr h)
              }
            }
            {
              intro h
              cases h
              {
                rename_i a_eq_three
                exact Or.inr (Or.inl a_eq_three)
              }
              rename_i h
              cases h
              {
                rename_i a_eq_n
                exact Or.inl a_eq_n
              }
              {
                rename_i h
                exact Or.inr (Or.inr h)
              }
            }
          }
        }
      }
      rename_i h
      cases h
      {
        apply Or.inl
        assumption
      }
      rename_i h
      cases h
      {
        apply Or.inr
        apply Or.inl
        assumption
      }
      {
        rename_i med_ten
        rw [median] at med_ten
        simp only [List.head_tail, List.getElem_tail, Nat.reduceAdd] at med_ten
        cases Nat.lt_or_ge n 10
        {
          rename_i n_lt_ten
          suffices ten_sorted_last : (Finset.sort (fun x1 x2 => x1 ≤ x2) {n, 3, 6, 9, 10})[(Finset.sort (fun x1 x2 => x1 ≤ x2) {n, 3, 6, 9, 10}).length - 1] = ({n, 3, 6, 9, 10} : Finset ℕ).max' _
          {
            simp only [Finset.length_sort] at ten_sorted_last
            suffices s_card_five : ({n, 3, 6, 9, 10} : Finset ℕ).card = 5
            {
              simp only [s_card_five, Nat.add_one_sub_one] at ten_sorted_last
              suffices ten_max : ({n, 3, 6, 9, 10} : Finset ℕ).max' _ = 10
              {
                rw [ten_max] at ten_sorted_last
                suffices two_eq_four : 2 = 4
                {contradiction}
                {
                  apply (List.Nodup.getElem_inj_iff _).1
                  {
                    apply Eq.trans
                    exact med_ten
                    apply Eq.symm
                    exact ten_sorted_last
                  }
                  {
                    apply @Finset.sort_nodup ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩
                  }
                }
              }
              {
                apply Nat.le_antisymm
                {
                  apply (Finset.max'_le_iff {n, 3, 6, 9, 10} _).2
                  {
                    intro y y_in_s
                    simp only [Finset.mem_insert, Finset.mem_singleton] at y_in_s
                    cases y_in_s
                    {
                      rename_i y_eq
                      rw [y_eq]
                      apply Nat.le_of_lt
                      assumption
                    }
                    rename_i y_in_s
                    cases y_in_s
                    {
                      rename_i y_eq
                      rw [y_eq]
                      norm_num
                    }
                    rename_i y_in_s
                    cases y_in_s
                    {
                      rename_i y_eq
                      rw [y_eq]
                      norm_num
                    }
                    rename_i y_in_s
                    cases y_in_s
                    {
                      rename_i y_eq
                      rw [y_eq]
                      norm_num
                    }
                    {
                      apply Nat.le_of_eq
                      assumption
                    }
                  }
                  {
                    simp only [Finset.insert_nonempty]
                  }
                }
                {
                  apply Nat.ge_of_not_lt
                  intro max_lt_ten
                  suffices ten_lt_ten : 10 < 10
                  {contradiction}
                  {
                    apply (Finset.max'_lt_iff {n, 3, 6, 9, 10} _).1
                    assumption
                    simp only [Finset.mem_insert, Nat.reduceEqDiff, Nat.succ_ne_self,
                      Finset.mem_singleton, or_true]
                  }
                }
              }
            }
            {
              rw [Finset.card_insert_of_not_mem n_neq]
              simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
                not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
                Nat.reduceAdd]
            }
          }
          {
            apply Finset.sorted_last_eq_max'
          }
        }
        {
          rename_i n_ge_ten
          suffices ten_sorted_second_last : (Finset.sort (fun x1 x2 => x1 ≤ x2) {n, 3, 6, 9, 10})[3]'(by
            simp only [Finset.length_sort]
            rw [Finset.card_insert_of_not_mem n_neq]
            simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
              not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
              Nat.reduceLT]
          ) = 10
          {
            suffices two_eq_three : 2 = 3
            {contradiction}
            {
              apply (List.Nodup.getElem_inj_iff _).1
              {
                apply Eq.trans
                exact med_ten
                exact Eq.symm ten_sorted_second_last
              }
              {simp only [Finset.sort_nodup]}
            }
          }
          {
            suffices s_eq₂ : ({n, 3, 6, 9, 10} : Finset ℕ) = {3, 6, 9, 10, n}
            {
              simp only [s_eq₂, @Finset.sort_insert ℕ (fun x1 x2 => x1 ≤ x2) _ _ _ _ _
                3 {6, 9, 10, n} (by
                  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
                    Nat.reduceLeDiff, forall_eq, true_and]
                  apply @Nat.le_trans 3 10
                  norm_num
                  assumption
                ) (by
                  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, false_or]
                  intro three_eq_n
                  rw [←three_eq_n] at n_ge_ten
                  contradiction
                )]
              simp only [List.getElem_cons_succ, @Finset.sort_insert ℕ (fun x1 x2 => x1 ≤ x2) _ _ _ _ _
                6 {9, 10, n} (by
                  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
                    Nat.reduceLeDiff, forall_eq, true_and]
                  apply @Nat.le_trans 6 10
                  norm_num
                  assumption
                ) (by
                  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, false_or]
                  intro six_eq_n
                  rw [←six_eq_n] at n_ge_ten
                  contradiction
                )]
              simp only [@Finset.sort_insert ℕ (fun x1 x2 => x1 ≤ x2) _ _ _ _ _
                9 {10, n} (by
                  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
                    Nat.reduceLeDiff, forall_eq, true_and]
                  apply @Nat.le_trans 9 10
                  norm_num
                  assumption
                ) (by
                  simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, false_or]
                  intro nine_eq_n
                  rw [←nine_eq_n] at n_ge_ten
                  contradiction
                ), List.getElem_cons_succ]
              apply Eq.trans
              {
                exact @Finset.sorted_zero_eq_min' ℕ _ {10, n} (by
                    simp only [Finset.length_sort, Finset.card_pos, Finset.insert_nonempty]
                  )
              }
              {
                apply Nat.le_antisymm
                {
                  apply Nat.le_of_not_gt
                  intro min_gt_10
                  suffices : 10 < 10
                  {contradiction}
                  {
                    apply (Finset.lt_min'_iff {10, n} (by simp only [Finset.insert_nonempty])).1
                    assumption
                    simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
                  }
                }
                {
                  apply (Finset.lt_min'_iff {10, n} (by simp only [Finset.insert_nonempty])).2
                  intro y y_in_pair
                  simp only [Finset.mem_insert, Finset.mem_singleton] at y_in_pair
                  cases y_in_pair
                  {
                    rename_i y_eq_ten
                    rw [y_eq_ten]
                    norm_num
                  }
                  {
                    rename_i y_eq_n
                    rw [y_eq_n]
                    apply Nat.lt_of_succ_le
                    exact n_ge_ten
                  }
                }
              }
            }
            {
              ext
              rename_i a
              simp only [Finset.mem_insert, Finset.mem_singleton]
              apply Iff.intro
              {
                intro h
                cases h
                {
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  assumption
                }
                rename_i h
                cases h
                {
                  apply Or.inl
                  assumption
                }
                rename_i h
                cases h
                {
                  apply Or.inr
                  apply Or.inl
                  assumption
                }
                rename_i h
                cases h
                {
                  apply Or.inr
                  apply Or.inr
                  apply Or.inl
                  assumption
                }
                {
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inl
                  assumption
                }
              }
              {
                intro h
                cases h
                {
                  apply Or.inr
                  apply Or.inl
                  assumption
                }
                rename_i h
                cases h
                {
                  apply Or.inr
                  apply Or.inr
                  apply Or.inl
                  assumption
                }
                rename_i h
                cases h
                {
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inl
                  assumption
                }
                rename_i h
                cases h
                {
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  assumption
                }
                {
                  apply Or.inl
                  assumption
                }
              }
            }
          }
        }
      }
    }
    {
      rw [median]
      apply (@Finset.mem_sort ℕ Nat.le
        Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩
        {n, 3, 6, 9, 10} ((@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 3, 6, 9, 10}).tail.tail.head
        (by
          intro tail_tail_nil
          rw [←@Finset.length_sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 3, 6, 9, 10}] at card_five
          rw [←@List.cons_head!_tail ℕ _ (@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 3, 6, 9, 10}) (by
            intro s_nil
            rw [s_nil] at card_five
            contradiction
          ), List.length_cons] at card_five
          rw [←@List.cons_head!_tail ℕ _ (@Finset.sort ℕ Nat.le Nat.decLe ⟨by apply Nat.le_trans⟩ ⟨by apply Nat.le_antisymm⟩ ⟨by apply Nat.le_total⟩ {n, 3, 6, 9, 10}).tail (by
            intro s_nil
            rw [s_nil] at card_five
            contradiction
          ), List.length_cons, tail_tail_nil] at card_five
          contradiction
        ))).1
      simp only [List.head_tail, List.getElem_tail, Nat.reduceAdd, List.getElem_mem]
    }
  }
  {
    intro n_eq
    rw [Finset.card_insert_of_mem n_eq] at card_five
    simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
      Nat.reduceAdd] at card_five
  }
}