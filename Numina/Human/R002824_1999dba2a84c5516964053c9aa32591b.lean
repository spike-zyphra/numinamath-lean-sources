import Mathlib

/- # Problem:
 11.3. All 100 natural numbers from 2 to 101 were divided into two groups of 50 numbers each. The numbers in each group were multiplied, and the two resulting products were added. Prove that this sum is a composite number.
Решение: Заметим, что в результате описанного действия всегда получится натуральное число, большее 101. Возможны два случая.

1. В каждой группе есть чётное число. Тогда произведение чисел в каждой из групп чётна, как и сумма этих произведений. Чётное число, большее 2 - составное, утверждение в этом случае доказано.
2. Все чётные числа попали в одну группу. Тогда (так как в наборе чётных чисел ровно 50) одна из групп содержит все чётные числа, вторая - все нечётные. В каждой группе, следовательно есть числа, кратные 3 (можно аналогично рассуждать с делимостью на 5,7 , и т. д.); тогда каждое из произведений, также как и их сумма тоже делится на 3. Натуральное число, большее 3 и делящееся на 3 - составное. Утверждение доказано и в этом случае тоже.

Рекомендации по проверке:

есть в работебаллыВерное доказательство7 балловВ приведённом доказательстве не рассмотрен принципиально важный случай3 баллаУтверждение проиллюстрировано на примерах0 баллов -/
theorem number_theory_118807 (S1 S2 : Finset ℕ)
    (hS1 : S1 ⊆ Finset.Icc 2 101) (hS2 : S2 ⊆ Finset.Icc 2 101)
    (hS12 : S1 ∩ S2 = ∅) (hS1' : S1.card = 50) (hS2' : S2.card = 50) :
    ¬ Nat.Prime (∏ x ∈ S1, x + ∏ x ∈ S2, x) := by

  have h_prod_S1_range : 1 < ∏ x ∈ S1, x := by
    rw [show 1 = ∏ x ∈ S1, 1 by simp]
    apply Finset.prod_lt_prod_of_nonempty
    . intro x hx
      norm_num
    . intro x hx
      have := hS1 hx
      simp at this
      omega
    . rw [← Finset.one_le_card, hS1']
      norm_num
  have h_prod_S2_range : 1 < ∏ x ∈ S2, x := by
    rw [show 1 = ∏ x ∈ S2, 1 by simp]
    apply Finset.prod_lt_prod_of_nonempty
    . intro x hx
      norm_num
    . intro x hx
      have := hS2 hx
      simp at this
      omega
    . rw [← Finset.one_le_card, hS2']
      norm_num


  by_contra h_contra
  by_cases h1 : (∃ x1 ∈ S1, Even x1) ∧ (∃ x2 ∈ S2, Even x2)
  . have h2 : 2 ∣ ∏ x ∈ S1, x := by
      have ⟨x1, hx1, hx1'⟩ := h1.1
      have hd1 : 2 ∣ x1 := Even.two_dvd hx1'
      have hd2 : x1 ∣ ∏ x ∈ S1, x := by
        apply Finset.dvd_prod_of_mem
        exact hx1
      exact Nat.dvd_trans hd1 hd2
    have h3 : 2 ∣ ∏ x ∈ S2, x := by
      have ⟨x2, hx2, hx2'⟩ := h1.2
      have hd1 : 2 ∣ x2 := Even.two_dvd hx2'
      have hd2 : x2 ∣ ∏ x ∈ S2, x := by
        apply Finset.dvd_prod_of_mem
        exact hx2
      exact Nat.dvd_trans hd1 hd2
    have h4 : 2 ∣ ∏ x ∈ S1, x + ∏ x ∈ S2, x := Nat.dvd_add h2 h3
    have := Nat.Prime.eq_two_or_odd h_contra
    rcases this with h | h
    all_goals omega
  . wlog h2 : ∀ x ∈ S1, Odd x
    . rw [Finset.inter_comm] at hS12
      rw [add_comm] at h_contra
      rw [and_comm] at h1
      apply this S2 S1
      all_goals try assumption
      simp at h1 h2
      intro x hx
      have := h1 x hx
      by_contra h
      simp only [Nat.not_odd_iff_even] at h
      obtain ⟨y, hy1, hy2⟩ := h2
      have := this h y hy1
      contrapose this
      simp only [Nat.not_odd_iff_even]
      exact hy2
    . let S_odd := (Finset.Icc 2 101).filter (fun x => Odd x)
      have h_S_odd_card : S_odd.card = 50 := by decide
      have h_S1_eq_odd : S1 = S_odd := by
        apply Finset.eq_of_subset_of_card_le
        . intro x hx
          unfold S_odd
          simp only [Finset.mem_filter]
          exact ⟨hS1 hx, h2 x hx⟩
        . rw [h_S_odd_card, hS1']

      have h3 : 3 ∈ S1 := by
        rw [h_S1_eq_odd]
        unfold S_odd
        simp
        use 1
        norm_num

      have h4 : 6 ∈ S2 := by
        have : (S1 ∪ S2) = Finset.Icc 2 101 := by
          apply Finset.eq_of_subset_of_card_le
          . apply Finset.union_subset
            . exact hS1
            . exact hS2
          . have := Finset.card_inter_add_card_union S1 S2
            rw [hS12, hS1', hS2'] at this
            simp at this
            rw [this, show (Finset.Icc 2 101).card = 100 by decide]
        have : 6 ∈ (S1 ∪ S2) := by
          rw [this]
          decide
        simp at this
        rcases this with h | h
        . rw [h_S1_eq_odd] at h
          unfold S_odd at h
          simp at h
          contrapose h
          simp
          use 3
        . exact h

      have h5 : 3 ∣ ∏ x ∈ S1, x + ∏ x ∈ S2, x := by
        have hd1 : 3 ∣ ∏ x ∈ S1, x := by
          apply Finset.dvd_prod_of_mem
          exact h3
        have hd2 : 6 ∣ ∏ x ∈ S2, x := by
          apply Finset.dvd_prod_of_mem
          exact h4
        replace hd2 := Nat.dvd_trans (show 3 ∣ 6 by omega) hd2
        exact Nat.dvd_add hd1 hd2

      have h6 : 3 = ∏ x ∈ S1, x + ∏ x ∈ S2, x := by
        rw [Nat.prime_def] at h_contra
        obtain ⟨h7, h8⟩ := h_contra
        have := h8 3 h5
        simp at this
        exact this

      omega
