import Mathlib
import Aesop

open Finset

theorem algebra_600625
    (a : ℕ → ℕ)
    (h₀ : ∀ n, a n = if (n∈Icc 1 5) then n else (∏ i ∈ Ico 1 n, a i) - 1) :
    ∏ i ∈ Icc 1 70, a i = ∑ i ∈ Icc 1 70, (a i)^2 := by
  have h_prod_6: ∏ x ∈ Ico 1 6, a x = 120 := by
    repeat rw [prod_eq_prod_Ico_succ_bot (by linarith)]
    repeat rw [h₀]
    simp
  have h_sum_6: ∑ x ∈ Ico 1 6, (a x)^2 = 55 := by
    repeat rw [sum_eq_sum_Ico_succ_bot (by linarith)]
    repeat rw [h₀]
    simp
  have h_a_6: a 6 = 119 :=  by
    have h₁ := h₀ 6
    simp at h₁
    rw [h₀, if_neg, h_prod_6]
    simp [h₁]
  have h_ico: ∀n ≥ 6, Ico 1 n = Ico 1 6 ∪ Ico 6 n := by
    intro n h
    symm
    apply Ioc_union_Ioc_eq_Ioc (by simp) (by simp; apply Nat.le_sub_of_add_le; linarith )
  have h_ico_disj: ∀n ≥ 6, Disjoint (Ico 1 6) (Ico 6 n) := by
    intro n h
    apply Ico_disjoint_Ico_consecutive
  have h_prod_split_6 {n: ℕ}: n ≥ 6 -> ∏ i ∈ Ico 1 n, a i = 120 * ∏ x ∈ Ico 6 n, a x := by
    intro h
    rw [h_ico _ h, prod_union (h_ico_disj _ h), h_prod_6]
  have h_a_n_eq_prod_6: ∀n ≥ 6, a n = 120 * ∏ x ∈ Ico 6 n, a x - 1 := by
    intro n hn
    rw [h₀, if_neg (by simp; bound), h_prod_split_6 hn]

  have h_a_ge_1 {n: ℕ}: 6 ≤ n → a n ≥ 1 := by
    intro h
    induction' n using Nat.strong_induction_on
    · rename_i n' a_ih
      rw [h_a_n_eq_prod_6 n' h]
      apply le_trans  (b := 119)
      · simp
      · apply Nat.le_sub_of_add_le
        simp
        have h' := pow_card_le_prod (Ico 6 n') a 1 (by intro x; simp_intro hx;  apply a_ih x hx.2 hx.1)
        simpa [h'] using h'
  have h_pow_card_le_prod {n: ℕ}: n ≥ 6 → 1 ≤ ∏ x ∈ Ico 6 n, a x := by
    intro h
    have h' := pow_card_le_prod (Ico 6 n) a 1
    simp at h'
    apply h'
    intro x hx _
    apply h_a_ge_1 hx

  have h_prod_eq_add_one {n: ℕ}: n≥6 → ∏ i ∈ Ico 1 n, a i = a n + 1 := by
    intro h
    rw [h_a_n_eq_prod_6 n h, Nat.sub_add_cancel, h_prod_split_6 h]
    rw [<-one_mul (a := 1)]
    apply Nat.mul_le_mul (by simp)
    apply le_trans _ (h_pow_card_le_prod h)
    bound

  have h_a_mono (n: ℕ) (m: ℕ): n ≥ 6 → n ≤ m → a n ≤ a m := by
    intro h hnm
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hnm
    apply Nat.le_of_add_le_add_right (b := 1)
    rw [hk, <-h_prod_eq_add_one (by linarith), <-h_prod_eq_add_one (by linarith), add_comm]
    rw [<-Ico_union_Ico_eq_Ico (b := n) (c := n + k) (by linarith) (by linarith)]
    rw [prod_union (Ico_disjoint_Ico_consecutive 1 n (n+k))]
    apply Nat.le_mul_of_pos_right
    simp
    intros
    apply lt_of_lt_of_le (b := 1) (by simp)
    apply h_a_ge_1 (by bound)


  have h_a_n_succ (n: ℕ): 6 ≤ n → (a (n + 1) - a n) + 1 = (a n)^2 := by
    intro h
    have h₁ := h₀ n
    have h₂ := h₀ (n + 1)
    rw [if_neg (by simp; bound)] at h₁ h₂
    rw [h₂, Finset.prod_Ico_succ_top (by bound), h_prod_eq_add_one h]
    have h_a_n: a n ≥ 1 := by apply h_a_ge_1; linarith
    rw [add_mul, <-Nat.sub_add_comm, Nat.sub_add_cancel]
    · simp; ring_nf
    · simp; nlinarith
    · apply Nat.le_sub_of_add_le
      nlinarith
  have h₀': ∑ i ∈ Icc 1 70, a i ^ 2 = 55 + ∑ i∈Ico 6 71, (a i)^2 := by
    simp [<-Nat.Ico_succ_right]
    rw [h_ico _ (by linarith), sum_union (h_ico_disj _ (by linarith)), h_sum_6]
  have h₁: ∑ i∈Ico 6 71, (a i)^2 = ∑ i∈Ico 6 71, (a (i + 1) - a i + 1) := by
    apply sum_congr rfl
    intro x hx
    rw [<-h_a_n_succ]
    simp at hx
    exact hx.1
  have h₂: ∑ i∈Ico 6 71, (a (i + 1) - a i + 1) = a 71 - a 6 + 65 := by
    simp [sum_add_distrib ]
    simp [sum_Ico_eq_sum_range]
    let a' (i: ℕ) := a (6 + i)

    have h': ∑ k ∈ range 65, (a (6 + k + 1) - a (6 + k)) = ∑ i ∈ range 65, (a' (i + 1) - a' i) := by
      apply sum_congr rfl
      unfold a'
      intros; rfl
    rw [h', sum_range_tsub]
    intro x y hx
    unfold a'
    apply h_a_mono _ _ <;> try simp; try assumption
  rw [h₀', h₁, h₂, h_a_6, h₀, if_neg (by simp)]
  ring_nf
  simp [<-Nat.sub_add_eq]
  rw [<-Nat.add_sub_assoc, Nat.add_sub_self_left]
  · rfl
  · rw [h_prod_split_6 (by simp)]
    simp
    apply h_pow_card_le_prod (by linarith)
