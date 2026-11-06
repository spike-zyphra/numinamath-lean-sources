import Mathlib

open Nat
set_option maxHeartbeats 400000

lemma sum_eq_pair {n} (pos_n : 0 < n) : ∑ i ∈ Finset.range (10^(n+1)), (digits 10 i).sum =
    ∑ p ∈ Finset.range (10^n) ×ˢ Finset.range 10, (digits 10 (10 * p.fst + p.snd)).sum := by
  have h1 : ∀ x ∈ Finset.range (10^(n+1)),
      (x / 10, x % 10) ∈ Finset.range (10^n) ×ˢ Finset.range (10^n) := by
    intro x x_in_s
    simp_all [Nat.pow_add_one']
    have : 10 ≤ 10^n := by
      suffices 1 ≤ 10 ^ (n - 1) by
        have : 10 ≤ 10 * 10 ^ (n - 1) := by
          linarith
        rw [<- Nat.pow_add_one'] at this
        rwa [Nat.sub_add_cancel pos_n] at this

      exact one_le_pow _ _ (by simp)

    omega

  rw [Finset.sum_bij (fun x x_in => (x / 10, x % 10))]
  · intro x x_in
    simp_all [Nat.pow_add_one', Nat.mod_lt]

  · simp
    intro i hi j j_lt f_eq
    omega

  · simp
    intro j k j_lt k_lt
    use 10 * j + k
    omega

  · simp
    intro i i_in_s
    congr!
    exact Eq.symm (div_add_mod i 10)


lemma digits_sum_base_mul_eq {n} :
    (digits 10 (n * 10)).sum = (digits 10 n).sum := by
  by_cases pos_n : n = 0
  · simp [pos_n]

  have digits_mul_10 : digits 10 (n * 10) = 0 :: digits 10 n := by
    have := Nat.digits_base_pow_mul (by simp : 1 < 10)
      (by exact zero_lt_of_ne_zero pos_n : 0 < n) (k := 1)
    simp only [mul_comm] at this
    exact this

  cases' n with n
  · simp
  · rw [digits_mul_10]
    simp

theorem number_theory_641519 (k : ℕ) (hk : 0 < k) :
    (∑ n ∈ Finset.Ico 1 (10^k), (digits 10 n).sum) = 45 * k * 10^(k-1) := by
  induction' k, (by linarith : 1 ≤ k) using Nat.le_induction with m ge ih
  · simp [show Finset.Ico 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9} by rfl]
  · specialize ih ge
    have pos_m : 0 < m := by positivity

    have digits_eq_cons := Nat.digits_eq_cons_digits_div
      (by simp : 1 < 10) (by linarith)

    have pos_n : ∀ n ∈ Finset.Ico 1 (10^m), 0 < n := by
      intro n n_in
      simp at n_in
      exact n_in.left

    have {n} : ∑ n ∈ Finset.Ico 1 (10 ^ n), (digits 10 n).sum =
        ∑ n ∈ Finset.range (10 ^ n), (digits 10 n).sum := by
      simp [Finset.sum_range_eq_add_Ico]

    rw [this] at ih ⊢
    clear this
    rw [@sum_eq_pair m ge]

    have : ∑ p ∈ Finset.range (10 ^ m) ×ˢ Finset.range 10, (digits 10 (10 * p.1 + p.2)).sum =
        ∑ p ∈ Finset.range (10 ^ m) ×ˢ Finset.range 10,
        ((digits 10 (10 * p.1)).sum + (digits 10 p.2).sum) := by
      apply Finset.sum_congr rfl
      intro p hp
      have h : p.2 < 10 := by
        rw [Finset.mem_product] at hp
        exact Finset.mem_range.mp hp.2

      have digit_sum_add_single_digit (n d : ℕ) (hd : d < 10) :
        (digits 10 (10 * n + d)).sum = (digits 10 (10 * n)).sum + (digits 10 d).sum := by
        cases' d with d
        · simp [digits]
        · have hd' : d + 1 < 10 := hd
          simp [List.sum_cons, List.sum_nil]
          rw [show (d + 1) % 10 = d + 1 by exact mod_eq_of_lt hd]
          simp [add_comm]
          rw [Nat.add_div (by simp)]
          simp
          split_ifs with mod_le
          · simp_all
            omega
          · simp_all [div_eq_of_lt hd, mod_eq_of_lt hd]
            rw [<- digits_sum_base_mul_eq, mul_comm]


      exact digit_sum_add_single_digit p.1 p.2 h

    rw [this]
    clear this
    rw [@Finset.sum_product]
    simp [Finset.sum_add_distrib]
    simp [show Finset.range 10 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} by rfl]
    ring_nf
    congr
    conv_rhs => rw [show 10 ^ m = 10 * 10 ^ (m - 1) by
      rw [<- Nat.pow_add_one']
      simp
      omega
    ]
    conv_lhs =>
      simp [mul_comm 10, <- Finset.sum_mul]
    suffices ∑ i ∈ Finset.range (10^m), (digits 10 (i * 10)).sum = m * 10 ^ (m - 1) * 45 by
      linarith
    ring_nf at ih
    have : ∑ i ∈ Finset.range (10 ^ m), (digits 10 (i * 10)).sum =
      ∑ i ∈ Finset.range (10 ^ m), (digits 10 i).sum := by
      congr! 1 with i i_in
      simp at i_in
      exact digits_sum_base_mul_eq

    rw [this]
    exact ih
