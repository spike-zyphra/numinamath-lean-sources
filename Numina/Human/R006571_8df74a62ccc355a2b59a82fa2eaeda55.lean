import Mathlib
open Nat
noncomputable section

/-Let $C_Y$ be the integer $2000$. A person is born in a positive year $x < C_Y$. In the year $C_Y$, the person's age is $C_Y - x$. This age is equal to the sum of the digits of their birth year $x$. Show that the birth year $x$ is $1981$.-/
theorem number_theory_2000 (x : ℕ) (h₀ : x < 2000) (h₁ : x > 0) (hₓ : 2000 - x = (Nat.digits 10 x).sum) :
  x = 1981 := by
  -- Prove $(Nat.digits 10 x).sum ≤ 9 * 4 = 36$.
  have h_sum_le_36 : (Nat.digits 10 x).sum ≤ 36 := by
    have h_x_le_1999 : x ≤ 1999 := by linarith [h₀]
    have h_digits_len_le_4 : (Nat.digits 10 x).length ≤ 4 := by
      simpa using Nat.le_digits_len_le 10 x 1999 h_x_le_1999
    have h_digit_le_9 : ∀ d ∈ Nat.digits 10 x, d ≤ 9 := by
      intros d hd
      apply Nat.le_of_lt_succ
      simpa using Nat.digits_lt_base (by norm_num) hd
    have h_sum_le_len_times_9 : (Nat.digits 10 x).sum ≤ (Nat.digits 10 x).length * 9 := by
      apply List.sum_le_card_nsmul
      intros d hd
      apply h_digit_le_9 d hd
    nlinarith
  have h_x_ge_1964 : x ≥ 1964 := by omega
  -- Express $x = 1900 + 10k + l$, where $2 ≤ k ≤ 9, 0 ≤ l ≤ 9$.
  have h_x_form : ∃ k l : ℕ, 0 ≤ k ∧ k ≤ 9 ∧ 0 ≤ l ∧ l ≤ 9 ∧ x = 1900 + 10 * k + l := by
    have h_x_lt_2000 : x < 2000 := h₀
    have h_x_ge_1960 : x ≥ 1960 := by linarith
    obtain ⟨m, h_x_eq_1960_m⟩ := Nat.exists_eq_add_of_le h_x_ge_1960
    have h_m_lt_100 : m < 100 := by
      rw [h_x_eq_1960_m] at h_x_lt_2000
      linarith
    let k := m / 10
    let l := m % 10
    have h_m_eq_10k_l : m = 10 * k + l := by omega
    exists k + 6, l
    constructor
    · apply Nat.zero_le
    constructor
    · omega
    constructor
    · apply Nat.zero_le
    constructor
    · apply Nat.le_of_lt_succ
      apply Nat.mod_lt
      norm_num
    · rw [h_x_eq_1960_m, h_m_eq_10k_l]
      ring
  -- Substitute into the equation, compute the sum of digits.
  obtain ⟨k, l, h_k_ge_0, h_k_le_9, h_l_ge_0, h_l_le_9, h_x_eq_1900_10k_l⟩ := h_x_form
  have h_eq_substituted : 2000 - (1900 + 10 * k + l) = (Nat.digits 10 (1900 + 10 * k + l)).sum := by
    rw [h_x_eq_1900_10k_l] at hₓ
    exact hₓ
  -- Compute $(Nat.digits 10 (1900 + 10k + l)).sum = 1 + 9 + k + l$.
  have h_digits_sum : (Nat.digits 10 (1900 + 10 * k + l)).sum = 1 + 9 + k + l := by
    have h_digits_eq_list : Nat.digits 10 (1900 + 10 * k + l) = [l, k, 9, 1] := by
      have h_mod_div_1 : (1900 + 10 * k + l) % 10 = l ∧ (1900 + 10 * k + l) / 10 = 190 + k := by omega
      have h_mod_div_2 : (190 + k) % 10 = k ∧ (190 + k) / 10 = 19 := by omega
      have h_digits_first : Nat.digits 10 (1900 + 10 * k + l) =
                            l :: (Nat.digits 10 (190 + k)) := by
        have h_digits_apply : Nat.digits 10 (1900 + 10 * k + l) =
                            (1900 + 10 * k + l) % 10 :: Nat.digits 10 ((1900 + 10 * k + l) / 10) := by
          apply Nat.digits_of_two_le_of_pos
          · norm_num
          · nlinarith
        rw [h_mod_div_1.left, h_mod_div_1.right] at h_digits_apply
        exact h_digits_apply
      have h_digits_second : Nat.digits 10 (190 + k) = k :: (Nat.digits 10 19) := by
        have h_digits_apply : Nat.digits 10 (190 + k) =
                            (190 + k) % 10 :: Nat.digits 10 ((190 + k) / 10) := by
          apply Nat.digits_of_two_le_of_pos
          · norm_num
          · nlinarith
        rw [h_mod_div_2.left, h_mod_div_2.right] at h_digits_apply
        apply h_digits_apply
      have h_digits_19 : Nat.digits 10 19 = [9, 1] := by norm_num
      rw [h_digits_first, h_digits_second, h_digits_19]
    have h_sum_eq_list_sum : (Nat.digits 10 (1900 + 10 * k + l)).sum = [l, k, 9, 1].sum := by
      rw [h_digits_eq_list]
    rw [h_sum_eq_list_sum]
    simp [List.sum]
    linarith
  -- Derive $k$, $$l, and conclude $x = 1981$.
  have h_eq_11k_2l : 11 * k + 2 * l = 90 := by omega
  have h_2l_bounds : 2 ≤ 2 * l ∧ 2 * l ≤ 18 := by omega
  have h_11k_bounds : 72 ≤ 11 * k ∧ 11 * k ≤ 88:= by omega
  -- Solve for $k$, get $ 72/11 ≤ k ≤ 88/11 $, deduce $k = 4, l = 5$.
  have h_k_bounds : 7 ≤  k ∧ k ≤ 8 := by omega
  -- When $k=7$, $l$ is not an integer, deduce $k=8$.
  have h_k_eq_8 : k = 8 := by omega
  have h_l_eq_1 : l = 1 := by
    rw [h_k_eq_8] at h_eq_11k_2l
    apply Nat.eq_of_mul_eq_mul_left (by nlinarith)
    norm_num at h_eq_11k_2l
    nlinarith
  -- Conclude $x = 1981$.
  have h_x_eq : x = 1981 := by
    rw [h_x_eq_1900_10k_l, h_k_eq_8, h_l_eq_1]
  exact h_x_eq
