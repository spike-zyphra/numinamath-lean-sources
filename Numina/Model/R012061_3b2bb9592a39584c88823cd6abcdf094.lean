import Mathlib
open Real Finset Set 

theorem number_theory_605678 : ∀ n : Nat, n + (Nat.digits 10 n).sum = 1964 ↔ n = 1945 := by
  intro n
  constructor
  · 
    intro h_eq_1964
    have h_sum_le_36 : (Nat.digits 10 n).sum ≤ 36 := by
      have h_n_le_1964 : n ≤ 1964 := by omega
      have h_digits_len_le_4 : (Nat.digits 10 n).length ≤ 4 := by
        simpa using Nat.le_digits_len_le 10 n 1964 h_n_le_1964
      have h_digit_le_9 : ∀ d ∈ Nat.digits 10 n, d ≤ 9 := by
        intros d hd
        apply Nat.le_of_lt_succ
        simpa using Nat.digits_lt_base (by nlinarith) hd
      have h_sum_le_len_times_9 : (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length * 9 := by
        apply List.sum_le_card_nsmul
        intros d hd
        apply h_digit_le_9 d hd
      nlinarith
    have h_n_ge_1928 : n ≥ 1928 := by nlinarith
    have h_n_form : ∃ k l : Nat, 2 ≤ k ∧ k ≤ 9 ∧ 0 ≤ l ∧ l ≤ 9 ∧ n = 1900 + 10 * k + l := by
      have h_n_lt_2000 : n < 2000 := by omega
      have h_n_ge_1920 : n ≥ 1920 := by nlinarith
      obtain ⟨m, h_n_eq_1920_m⟩ := Nat.exists_eq_add_of_le h_n_ge_1920
      have h_m_lt_72 : m < 72 := by 
        have : m < 2000 - 1928 := by omega
        apply lt_of_lt_of_le this
        norm_num
      let k := m / 10
      let l := m % 10
      have h_m_eq_10k_l : m = 10 * k + l := by omega
      exists k + 2, l
      constructor
      · apply Nat.le_add_left
      constructor
      · omega
      constructor
      · apply Nat.zero_le
      constructor
      · apply Nat.le_of_lt_succ
        apply Nat.mod_lt
        norm_num
      · rw [h_n_eq_1920_m, h_m_eq_10k_l, ← add_assoc]
        ring
    obtain ⟨k, l, h_k_ge_2, h_k_le_9, h_l_ge_0, h_l_le_9, h_n_eq_1900_10k_l⟩ := h_n_form
    have h_eq_substituted : 1900 + 10 * k + l + (Nat.digits 10 (1900 + 10 * k + l)).sum = 1964 := by
      rw [h_n_eq_1900_10k_l] at h_eq_1964
      exact h_eq_1964
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
      all_goals omega
    have h_eq_11k_2l : 11 * k + 2 * l = 54 := by linarith 
    have h_k_bounds : 3 < k ∧ k ≤ 4 := by omega
    have h_k_eq_4 : k = 4 := by
      apply le_antisymm
      · apply h_k_bounds.right
      · apply Nat.le_of_lt_succ
        apply lt_of_le_of_lt h_k_bounds.left
        norm_num
    have h_l_eq_5 : l = 5 := by
      rw [h_k_eq_4] at h_eq_11k_2l
      apply Nat.eq_of_mul_eq_mul_left (by nlinarith)
      norm_num at h_eq_11k_2l
      nlinarith
    have h_n_eq_1945 : n = 1945 := by
      rw [h_n_eq_1900_10k_l, h_k_eq_4, h_l_eq_5]
    apply h_n_eq_1945
  · 
    intro h_eq_1945
    rw [h_eq_1945]
    norm_num