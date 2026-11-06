import Mathlib

set_option maxRecDepth 1000000

/-Let $n$ be a positive integer. Given that $n^{n}$ has 861 positive divisors, find $n$.-/
theorem number_theory_610356 (n : ℕ) (hn : n > 0) (h : (n ^ n).divisors.card = 861) :
    n = 20 := by
  rw [Nat.card_divisors (by simp), Nat.primeFactors_pow _ (by omega)] at h
  simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h
  obtain ⟨o, h₁⟩ := show ∃o, n.primeFactors.card = o by simp
  have h₂ : o ≤ 3 := by
    rw [h₁.symm]
    by_contra! h₁
    have h₃ : (∏ x ∈ n.primeFactors, (n * n.factorization x + 1)).factorization.sum (λ_ b ↦ b) = (861).factorization.sum (λ_ b ↦ b) := by rw [h.symm]
    rw [show (861 : ℕ).factorization.sum (λ_ b ↦ b) = 3 by native_decide, Nat.factorization_prod (fun x a ↦ (Nat.zero_ne_add_one (n * n.factorization x)).symm), Finsupp.sum_sum_index' (congrFun rfl) fun _ _ ↦ congrFun rfl] at h₃
    have h₄ : ∀m ≥ 2, 1 ≤ m.factorization.sum fun x b ↦ b := by
      intro m hm₁
      obtain ⟨p, hp₁, hp₂⟩ := show ∃ p, p.Prime ∧ p ∣ m by
        apply Nat.exists_prime_and_dvd
        omega
      have hp₃ := hp₂
      obtain ⟨k, hk⟩ := hp₃
      rw [hk, Nat.factorization_mul (Nat.Prime.ne_zero hp₁), Finsupp.sum_add_index' (congrFun rfl) fun _ _ ↦ congrFun rfl, Nat.Prime.factorization hp₁]
      · simp
      · rintro ⟨rfl⟩
        rw [hk] at hm₁
        norm_num at hm₁
    revert h₃
    simp only [imp_false, ←ne_eq]
    apply ne_of_gt
    have : 3 < ∑ x ∈ n.primeFactors, 1 := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      exact h₁
    apply lt_of_lt_of_le this
    apply Finset.sum_le_sum
    intro x hx
    apply h₄
    simp only [ge_iff_le, Nat.reduceLeDiff]
    apply le_trans (show 1 ≤ n by omega)
    apply Nat.le_mul_of_pos_right n
    rw [Nat.mem_primeFactors_of_ne_zero (by omega)] at hx
    apply Nat.Prime.factorization_pos_of_dvd hx.left hn.ne.symm hx.right
  interval_cases o
  · -- n.primeFactors.card = 0
    simp only [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h₁
    obtain (h₁ | h₁) := h₁ <;> rw [h₁] at h <;> norm_num at h
  · -- n.primeFactors.card = 1
    obtain ⟨p, hp₁⟩ := Finset.card_eq_one.mp h₁
    have hp₂ : p ∈ n.primeFactors := by rw [hp₁, Finset.mem_singleton]
    rw [Nat.mem_primeFactors_of_ne_zero (by omega)] at hp₂
    obtain ⟨hp₂, hp₃⟩ := hp₂
    obtain ⟨k, hk₁⟩ := show ∃k, n = p ^ k by
      use n.factorization p
      have h₁ : n.factorization = Finsupp.single p (n.factorization p) := by
        rw [←Finsupp.support_subset_singleton]
        simp only [Nat.support_factorization, hp₁, subset_refl]
      exact Nat.eq_pow_of_factorization_eq_single (by omega) h₁
    have h₁ : n.factorization = Finsupp.single p k := by
      rw [hk₁]
      exact Nat.Prime.factorization_pow (hp₂)
    rw [hp₁, h₁, hk₁] at h
    simp only [Finset.prod_singleton, Finsupp.single_eq_same, Nat.reduceEqDiff] at h
    have hk₂ : 2 ≤ k := by
      by_contra!
      interval_cases k <;> norm_num at h
      rw [h] at hp₂
      norm_num at hp₂
    have hp₂ : p ∈ (860).primeFactors := by
      rw [Nat.mem_primeFactors_of_ne_zero (by omega)]
      use hp₂
      rw [h.symm, Nat.Prime.dvd_mul hp₂]
      apply Or.inl
      exact (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod hk₁) n) hp₃).mp hp₃
    have : (860).primeFactors = {2, 5, 43} := by native_decide
    rw [this] at hp₂
    simp at hp₂
    obtain (hp₃ | hp₃ | hp₃) := hp₂ <;> rw [hp₃] at h
    · -- p = 2
      have h1 : k ≤ 9 := by
        by_contra
        have h3 : 2 ^ k * k ≥ 2 ^ 10 * 10 := by
          nlinarith [show 2 ^ k ≥ 2 ^ 10 by apply Nat.pow_le_pow_of_le_right (by norm_num) (by omega)]
        have h4 : 2 ^ 10 * 10 > 860 := by norm_num
        linarith
      interval_cases k <;> norm_num at h
    · -- p = 5
      have h : 5 ^ 2 ∣ 860 := by
        apply dvd_trans (pow_dvd_pow _ (show 2 ≤ k by omega))
        rw [←h]
        exact Nat.dvd_mul_right (5 ^ k) k
      norm_num at h
    · -- p = 43
      have h : 43 ^ 2 ∣ 860 := by
        apply dvd_trans (pow_dvd_pow _ (show 2 ≤ k by omega))
        rw [←h]
        exact Nat.dvd_mul_right (43 ^ k) k
      norm_num at h
  · -- n.primeFactors.card = 2
    obtain ⟨p, q, h₃, h₄⟩ := Finset.card_eq_two.mp h₁
    have hp₁ : p ∈ n.primeFactors := by
      rw [h₄]
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    have hq₁ : q ∈ n.primeFactors := by
      rw [h₄]
      simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
    rw [Nat.mem_primeFactors_of_ne_zero (by omega)] at hp₁ hq₁
    obtain ⟨hp₁, hp₂⟩ := hp₁
    obtain ⟨hq₁, hq₂⟩ := hq₁
    have h' := h
    rw [h₄, Finset.prod_insert (Finset.not_mem_singleton.mpr h₃)] at h
    simp only [Finset.prod_singleton, add_left_eq_self, mul_eq_zero] at h
    wlog h₆ : n * n.factorization p + 1 ≤ n * n.factorization q + 1 with h₇
    · rw [Finset.pair_comm] at h₄
      specialize h₇ n hn 0 h₁ (by simp) q p h₃.symm h₄
      specialize h₇ hq₁ hq₂ hp₁ hp₂
      apply h₇
      all_goals linarith
    have h₅ : (n * n.factorization p + 1, n * n.factorization q + 1) ∈ (861).divisorsAntidiagonal := by
      simp only [Nat.mem_divisorsAntidiagonal, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
      exact h
    rw [show Nat.divisorsAntidiagonal 861 = {(1, 861), (3, 287), (7, 123), (21, 41), (41, 21), (123, 7), (287, 3), (861, 1)} by native_decide] at h₅
    simp only [Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton] at h₅
    obtain (⟨h₅, h₇⟩ | ⟨h₅, h₇⟩ | ⟨h₅, h₇⟩ | ⟨h₅, h₇⟩ | h₅) := h₅
    · -- n * n.factorization p + 1 = 1 ∧ n * n.factorization q + 1 = 861
      simp only [add_left_eq_self, mul_eq_zero] at h₅
      apply False.elim
      revert h₅
      simp only [imp_false, not_or]
      use (by omega)
      apply Nat.ne_of_gt
      apply Nat.Prime.factorization_pos_of_dvd hp₁ (by omega) hp₂
    · -- n * n.factorization p + 1 = 3 ∧ n * n.factorization q + 1 = 287
      simp only [Nat.reduceEqDiff] at h₅ h₇
      have h₈ : (n, n.factorization p) ∈ (2).divisorsAntidiagonal := by
        simp only [Nat.mem_divisorsAntidiagonal, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        exact h₅
      rw [show Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} by native_decide] at h₈
      simp only [Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton] at h₈
      obtain (⟨h₈, h₉⟩ | ⟨h₈, h₉⟩) := h₈
      · -- n = 1
        rw [h₈] at h₇ h₅
        simp at h₇ h₅
      · -- n = 2
        have h₉ : n.factorization = Finsupp.single 2 1 := by
          rw [h₈]
          apply Nat.Prime.factorization (by norm_num)
        rw [h₉, h₈] at h₇ h₅
        have : (fun₀ | 2 => 1) q = 0 := by
          apply Finsupp.single_eq_of_ne
          intro h
          rw [h.symm] at h₇
          norm_num at h₇
        rw [this] at h₇
        norm_num at h₇
    · -- n * n.factorization p + 1 = 7 ∧ n * n.factorization q + 1 = 123
      simp only [Nat.reduceEqDiff] at h₅ h₇
      have h₈ : n.factorization p < n := by
        apply Nat.factorization_lt p
        omega
      have h₉ : (n, n.factorization p) ∈ (6).divisorsAntidiagonal := by
        simp only [Nat.mem_divisorsAntidiagonal, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        exact h₅
      rw [show Nat.divisorsAntidiagonal 6 = {(1, 6), (2, 3), (3, 2), (6, 1)} by native_decide] at h₉
      simp only [Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton] at h₉
      obtain (⟨h₉, h₁₀⟩ | ⟨h₉, h₁₀⟩ | h₉) := h₉
      · linarith
      · linarith
      obtain (⟨h₉, h₁₀⟩ | ⟨h₉, h₁₀⟩) := h₉
      · -- n = 3
        have hn₁ : n.factorization = Finsupp.single 3 1 := by
          rw [h₉]
          apply Nat.Prime.factorization (by norm_num)
        rw [hn₁, h₉] at h₅ h₇
        have : (fun₀ | 3 => 1) q = 0 := by
          apply Finsupp.single_eq_of_ne
          intro h
          rw [h.symm] at h₇
          norm_num at h₇
        rw [this] at h₇
        norm_num at h₇
      · -- n = 6
        rw [h₉] at h₇
        omega
    · -- n * n.factorization p + 1 = 21 ∧ n * n.factorization q + 1 = 41
      simp only [Nat.reduceEqDiff] at h₅ h₇
      have h₉ : n ≤ 20 := by
        rw [h₅.symm]
        apply Nat.le_mul_of_pos_right n
        apply Nat.Prime.factorization_pos_of_dvd hp₁ (by omega) hp₂
      suffices Finset.filter (λn ↦ ∏ x ∈ n.primeFactors, (n * n.factorization x + 1) = 861) (Finset.Icc 0 20) = {20} by
        have h : n ∈ Finset.filter (λn ↦ ∏ x ∈ n.primeFactors, (n * n.factorization x + 1) = 861) (Finset.Icc 0 20) := by
          simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and]
          exact ⟨h₉, h'⟩
        rw [this] at h
        simp only [Finset.mem_singleton] at h
        exact h
      native_decide
    obtain (⟨h₅, h₇⟩ | ⟨h₅, h₇⟩ | ⟨h₅, h₇⟩ | ⟨h₅, h₇⟩) := h₅
    all_goals linarith
  · -- n.primeFactors.card = 3
    have h₃ : ∏ x ∈ n.primeFactors, (n + 1) ≤ 861 := by
      rw [h.symm]
      apply Finset.prod_le_prod'
      intro i hi
      simp only [add_le_add_iff_right]
      apply Nat.le_mul_of_pos_right n
      rw [Nat.mem_primeFactors_of_ne_zero (by omega)] at hi
      apply Nat.Prime.factorization_pos_of_dvd hi.left (by omega) hi.right
    simp only [Finset.prod_const, h₁] at h₃
    have h₄ : n ≤ 8 := by
      by_contra h
      have h3 : (n + 1) ^ 3 ≥ 1000 := by
        rw [show 1000 = 10 ^ 3 by norm_num]
        apply Nat.pow_le_pow_of_le_left
        all_goals omega
      linarith
    apply False.elim
    revert h₁
    interval_cases n <;> native_decide
