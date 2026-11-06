import Mathlib
open Nat 
noncomputable section

-- Supplement some LCM operation lemmas missing in Lean $4.15$.
lemma lcm_eq_mul_div (m n : Nat) : Nat.lcm m n = m * n / Nat.gcd m n := rfl
lemma gcd_dvd_mul (m n : Nat) : Nat.gcd m n ∣ m * n := ⟨Nat.lcm m n, by simp [Nat.gcd_mul_lcm]⟩
lemma lcm_eq_left_iff_dvd {m n : Nat}: Nat.lcm m n = m ↔ n ∣ m := by
  refine (Nat.eq_zero_or_pos m).elim (by rintro rfl; simp) (fun hm => ?_)
  rw [lcm_eq_mul_div, Nat.div_eq_iff_eq_mul_left (gcd_pos_of_pos_left _ hm) (gcd_dvd_mul _ _),
    Nat.mul_left_cancel_iff hm, Eq.comm, gcd_eq_right_iff_dvd]

-- Auxiliary lemma: Compute the least common multiple of ${n, 2n, 3n}$.
lemma lcm_n_2n_3n (n : ℕ) (hn : n > 0) : Nat.lcm (Nat.lcm n (2 * n)) (3 * n) = 6 * n := by
  have h_lcm_n_2n : Nat.lcm n (2 * n) = 2 * n := by
    have h_n_dvd_2n : n ∣ 2 * n := by apply Nat.dvd_mul_left
    rw [lcm_comm, lcm_eq_left_iff_dvd]
    exact h_n_dvd_2n
  have h_lcm_2n_3n : Nat.lcm (2 * n) (3 * n) = 6 * n := by
    have h_2n_dvd_6n :  n ∣ 3 * n := by
      exists 3
      ring
    have h_3n_dvd_6n : 3 * n ∣ 6 * n := by
      exists 2
      ring
    have h_lcm_eq : Nat.lcm (2 * n) (3 * n) = (2 * n * (3 * n)) / Nat.gcd (2 * n) (3 * n) := by
      apply lcm_eq_mul_div
    have h_gcd : Nat.gcd (2 * n) (3 * n) = n := by
      have h_gcd_n : Nat.gcd (2 * n) (3 * n) = n * Nat.gcd 2 3 := by
        rw [mul_comm n]
        apply Nat.gcd_mul_right
      rw [h_gcd_n]
      norm_num
    rw [h_lcm_eq, h_gcd]
    have h_simp: 3 * n / n = 3  := by
      have : n ∣ n := Nat.dvd_refl n
      rw [Nat.mul_div_assoc 3 this,Nat.div_self (by linarith)]
    rw [Nat.mul_div_assoc,h_simp]
    ring_nf
    exact h_2n_dvd_6n
  rw [h_lcm_n_2n]
  exact h_lcm_2n_3n

/-9.3. Find all triples of distinct natural numbers, the least common multiple of which is equal to their sum. The least common multiple of several numbers is the smallest natural number that is divisible by each of these numbers.-/
theorem number_theory_607777 :
    ∀ a b c : ℕ, a < b ∧ b < c ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    Nat.lcm (Nat.lcm a b) c = a + b + c ↔
    ∃ n : ℕ, n > 0 ∧ a = n ∧ b = 2 * n ∧ c = 3 * n := by
  intro a b c
  constructor
  -- Forward direction: If $lcm(a, b, c) = a + b + c$, then $(a, b, c) = (n, 2n, 3n)$.
  · rintro ⟨h_ab, h_bc, h_ab_ne, h_bc_ne, h_ac_ne, h_lcm⟩
    have h_a_pos : a > 0 := by
      apply Nat.pos_of_ne_zero
      intro h_a_zero
      have h_a_eq : a = 0 := h_a_zero
      rw [h_a_eq] at h_ab
      have h_b_pos : b > 0 := by nlinarith
      have : Nat.lcm a b = 0 := by rw [h_a_eq]; exact_mod_cast Int.lcm_zero_left b
      have : Nat.lcm (Nat.lcm a b) c = 0 := by rw [this];exact_mod_cast Int.lcm_zero_left c
      linarith
    -- Show $c$ divides $a + b$, using $lcm(a, b, c) = a + b + c$ and $c$ divides $lcm(a, b, c)$/
    have h_c_dvd_sum : c ∣ a + b := by
      have h_lcm_dvd_c : c ∣ Nat.lcm (Nat.lcm a b) c := by apply Nat.dvd_lcm_right
      have h_lcm_eq_sum : Nat.lcm (Nat.lcm a b) c = a + b + c := by apply h_lcm
      rw [h_lcm_eq_sum] at h_lcm_dvd_c
      have h_c_dvd_sum : c ∣ a + b + c := by exact h_lcm_dvd_c
      have h_c_dvd_c : c ∣ c := by apply Nat.dvd_refl
      have h_sum_ge_c : a + b + c ≥ c := by apply Nat.le_add_left
      have h_dvd_diff : c ∣ a + b + c - c := by apply Nat.dvd_sub h_sum_ge_c h_c_dvd_sum h_c_dvd_c
      have h_diff_eq : (a + b + c) - c = a + b := by
        apply Nat.add_sub_cancel
      rw [← h_diff_eq]
      exact h_dvd_diff
    -- Establish $a + b = c$, combining $c$ divides $a + b$ with the constraint $a + b < 2c$.
    have h_a_b_sum : a + b = c := by
      have h_a_b_lt_2c : a + b < 2 * c := by
        have h_a_b_le : a + b ≤ b + b := by apply Nat.add_le_add_right (Nat.le_of_lt h_ab)
        have h_2b_lt_2c : 2 * b < 2 * c := by
          apply Nat.mul_lt_mul_of_pos_left h_bc
          norm_num
        linarith
      obtain ⟨k, hk⟩ := h_c_dvd_sum
      have h_k_lt_2 : k < 2 := by nlinarith
      have h_k_eq_1 : k = 1 := by nlinarith
      rw [h_k_eq_1] at hk
      linarith
    -- Prove $b$ divides $2a$, using $lcm(a, b, c) = 2a + 2b$ and $b$ divides $lcm(a, b, c)$.
    have h_b_dvd_2a : b ∣ 2 * a := by
      have h_b_dvd_lcm_ab : b ∣ Nat.lcm a b  := by
        apply Nat.dvd_lcm_right
      have h_lcm_ab_dvd_lcm_abc : Nat.lcm a b ∣ Nat.lcm (Nat.lcm a b) c := by apply Nat.dvd_lcm_left
      have h_b_dvd_lcm_abc : b ∣ Nat.lcm (Nat.lcm a b) c := by
        apply Nat.dvd_trans h_b_dvd_lcm_ab h_lcm_ab_dvd_lcm_abc
      have h_lcm_eq : Nat.lcm (Nat.lcm a b) c = a + b + c := by apply h_lcm
      have h_sum_eq : a + b + c = 2 * a + 2 * b := by
        rw [h_a_b_sum]
        linarith
      have h_b_dvd_sum : b ∣ 2 * a + 2 * b := by
        rw [← h_sum_eq, ← h_lcm_eq]
        exact h_b_dvd_lcm_abc
      have h_b_dvd_2b : b ∣ 2 * b := by rw [mul_comm];apply Nat.dvd_mul_right
      have h_sum_ge_2b : 2 * a + 2 * b ≥ 2 * b := by apply Nat.le_add_left
      have h_diff_eq : (2 * a + 2 * b) - 2 * b = 2 * a := by omega
      have h_dvd_diff : b ∣ (2 * a + 2 * b) - 2 * b := by
        apply Nat.dvd_sub h_sum_ge_2b h_b_dvd_sum h_b_dvd_2b
      rw [h_diff_eq] at h_dvd_diff
      exact h_dvd_diff
    have h_2a_eq_b : 2 * a = b := by
      have h_2a_lt_2b : 2 * a < 2 * b := by
        apply Nat.mul_lt_mul_of_pos_left h_ab
        norm_num
      obtain ⟨k, hk⟩ := h_b_dvd_2a
      have h_k_lt_2 : k < 2 := by nlinarith
      have h_k_eq_1 : k = 1 := by nlinarith
      rw [h_k_eq_1] at hk
      linarith
    have h_c_eq_3a : c = 3 * a := by linarith
    have h_solution : ∃ n : ℕ, n > 0 ∧ a = n ∧ b = 2 * n ∧ c = 3 * n := by
      exists a
      constructor
      · exact h_a_pos
      constructor
      · rfl
      constructor
      · exact h_2a_eq_b.symm
      · exact h_c_eq_3a
    exact h_solution
  -- Backward direction: If $(a, b, c) = (n, 2n, 3n)$, then lcm eq sum.
  · rintro ⟨n, hn_pos, h_a, h_b, h_c⟩
    have h_lcm_eq : Nat.lcm (Nat.lcm a b) c = 6 * n := by
      rw [h_a, h_b, h_c]
      apply lcm_n_2n_3n n hn_pos
    have h_sum : a + b + c = 6 * n := by
      rw [h_a, h_b, h_c]
      ring
    have h_conditions : a < b ∧ b < c ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c := by
      rw [h_a, h_b, h_c]
      constructor
      · nlinarith
      constructor
      · apply Nat.mul_lt_mul_of_pos_right
        norm_num
        exact hn_pos
      constructor
      · nlinarith
      constructor
      · nlinarith
      · nlinarith
    have h_lcm_sum : Nat.lcm (Nat.lcm a b) c = a + b + c := by
      rw [h_lcm_eq, h_sum]
    exact ⟨h_conditions.1, h_conditions.2.1, h_conditions.2.2.1, h_conditions.2.2.2.1, h_conditions.2.2.2.2, h_lcm_sum⟩
