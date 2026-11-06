import Mathlib

open Finset
theorem algebra_594514 {a : ℕ → ℝ} (ha : ∀ (n: ℕ), ∑ i ∈ Ico 1 (n + 1), a i = n ^ 2 - 4 * n + 2) :
    ∑ i ∈ Ico 1 11, |a i| = 66 := by
  have h1 : a 1 = -1 := by
    have h := ha 1
    simp at h
    linarith
  have h2 : a 2 = -1 := by
    have h := ha 2
    simp [sum_Ico_succ_top] at h
    linarith
  generalize hS: (λ(n: ℕ) => (n ^ 2:ℝ) - ((4 * n):ℝ) + 2) = S
  have h_S: ∀n, ∑ i ∈ Finset.Ico 1 (n + 1), a i = S n := by
    intro n
    simp [<-hS, ha]

  have h_a: ∀n ≥ 2, a (n + 1) = S (n + 1) - S n := by
    intro n hn
    rw [<-h_S n, <-h_S (n + 1), Finset.sum_Ico_succ_top (by linarith)]
    simp

  have h_abs: ∀n ≥ 3, a n ≥ 0 := by
    intro n
    rcases n with n | n <;> simp
    intro hn
    simp [h_a n hn, <-hS]
    ring_nf
    rw [<-sub_le_sub_iff_right (c := (n ^ 2: ℝ))]
    simp
    apply le_trans (b := 2 * (2:ℝ)) (by linarith)
    simp
    linarith

  have h_sum: ∑ i ∈ Ico 1 11, |a i| = ∑ i ∈ Ico 1 3, |a i| + ∑ i ∈ Ico 3 11, a i := by
    rw [<-sum_Ico_consecutive (n := 3) _ (by linarith) (by linarith)]
    simp
    apply sum_congr rfl
    intro x
    simp_intro hx
    apply h_abs x _
    linarith

  have h_sum': ∑ i ∈ Ico 3 11, a i = (∑ i ∈ Ico 1 11, a i) - a 1 - a 2 := by
    rw [sum_Ico_eq_sub _ (by linarith), sum_Ico_eq_sub _ (by linarith)]
    rw [sum_range_succ _ 2, sum_range_succ _ 1]
    simp
    rw [sub_sub, sub_sub, <-add_assoc]

  have ha_10 := ha 10
  rw [h_sum, Finset.sum_Ico_succ_top (by linarith), Finset.sum_Ico_succ_top (by linarith), h_sum']
  simp [ha_10, h1, h2]
  nlinarith
