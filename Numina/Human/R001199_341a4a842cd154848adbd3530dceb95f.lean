import Mathlib

theorem algebra_2452 {a : ℕ → ℝ} (ha1 : a 1 = 3) (ha2 : a 2 = 3)
    (han : ∀ n ≥ 2, a (n + 1) * a (n - 1) = a n ^ 2 + 2007) :
    ⌊(a 2007 ^ 2 + a 2006 ^ 2) / (a 2007 * a 2006)⌋ = 224 := by
  -- First, we prove that a₃ = 672.
  have h_a3 : a 3 = 672 := by
    have h_eq : a 3 * a 1 = a 2 ^ 2 + 2007 := han 2 (by norm_num)
    rw [ha1] at h_eq
    have h_a2_sq : a 2 ^ 2 = 9 := by
      rw [ha2]
      norm_num
    rw [h_a2_sq] at h_eq
    have h_calc : a 3 * 3 = 2016 := by
      rw [h_eq]
      norm_num
    have h3_ne_0 : (3 : ℝ) ≠ 0 := by norm_num
    have h_div : a 3 = 2016 / 3 := calc
      a 3 = (a 3 * 3) / 3 := by field_simp [h3_ne_0]
      _ = 2016 / 3 := by rw [h_calc]
    norm_num at h_div
    exact h_div

  -- Then, we prove that every term in the sequence is positive, using strong induction.
  have h_pos : ∀ n ≥ 2, a n > 0 := by
    intro n hn
    induction' n using Nat.strong_induction_on with n ih
    cases' Nat.eq_or_lt_of_le hn with h2 h2
    · -- Base case: n = 2
      subst h2
      rw [ha2]
      norm_num

      -- Inductive step: n > 2
    have h_ge_3 {m n : ℕ} (h : m > n) : m = n + 1 ∨ m ≥ n + 2 := by
      have h1 : n + 1 ≤ m := Nat.lt_iff_add_one_le.mp h
      have h2 : n + 1 = m ∨ n + 1 < m := Nat.eq_or_lt_of_le h1
      cases' h2 with h_eq h_lt
      · left
        exact eq_comm.mp h_eq
      · right
        exact Nat.lt_iff_add_one_le.mp h_lt
    cases' h_ge_3 h2 with h_eq_3 h_gt_3
    · -- Case n = 3
      subst h_eq_3
      have IH1 : a (3-1) > 0 := by
         have h2_ : (3:ℕ) - 1 ≥ 2 := by linarith
         apply ih (3-1)
         · linarith
         · exact h2_
      have IH2 : a (3-2) > 0 := by
        rw [ha1]
        linarith
      have h1 : a 3 * a (3 - 2) = a (3 - 1) ^ 2 + 2007 := by
        have h_ : 3 - 1 ≥ 2 := by linarith
        exact han (3 - 1) h_
      have h2 : a (3 - 1)^2 + 2007 > 0 := by
        apply add_pos
        · exact sq_pos_of_pos (GT.gt.lt (IH1))
        · norm_num
      rw [←h1] at h2
      exact (mul_pos_iff_of_pos_right IH2).mp h2
    · -- Case n > 3
      have n_pos : 0 < n := by linarith
      have hn_ge_1 : 1 ≤ n := by linarith
      have hn_ge_4 : n ≥ 4 := Nat.succ_le_of_lt h_gt_3
      have hn_minus_1 : n - 1 ≥ 2 := by exact Nat.le_sub_one_of_lt h2
      have hn_minus_1_lt_n : n - 1 < n := by apply Nat.pred_lt_self n_pos
      have hn_minus_2 : n - 2 ≥ 2 := by exact Nat.le_sub_of_add_le hn_ge_4
      have n_minus_2_lt_n : n-2 < n := by exact Nat.sub_lt (by linarith) (by norm_num)

      -- Apply the inductive hypothesis to n-1
      have IH1 : a (n - 1) > 0 := by
        apply ih (n - 1)
        · exact hn_minus_1_lt_n
        · exact hn_minus_1

      -- Apply the inductive hypothesis to n-2
      have IH2 : a (n - 2) > 0 := by
        apply ih (n - 2)
        · exact n_minus_2_lt_n
        · exact hn_minus_2

      -- From the recurrence relation, we have a n * a (n-2) = a (n-1)^2 + 2007
      have h1 : a n * a (n - 2) = a (n - 1) ^ 2 + 2007 := by
        have h_simp : n - 1 + 1 = n := by
          exact Nat.sub_add_cancel hn_ge_1
        have h_simp2 : n - 1 - 1 = n - 2 := by
          exact Nat.sub_sub n 1 1
        have := han (n - 1) hn_minus_1
        rw [h_simp, h_simp2] at this
        exact this

      -- The right-hand side is positive
      have h2 : a (n - 1) ^ 2 + 2007 > 0 := by
        apply add_pos
        · exact sq_pos_of_pos (GT.gt.lt (IH1))
        · norm_num

      -- Since a (n-2) > 0 and the product is positive, we have a n > 0
      rw [←h1] at h2
      exact (mul_pos_iff_of_pos_right IH2).mp h2

  -- We show that each term in the sequence (starting from n=2) is nonzero.
  have h_ne_zero : ∀ n ≥ 2, a (n) ≠ 0 := by
    intro n hn
    exact Ne.symm (ne_of_lt (h_pos n hn))

  -- We prove that for n ≥ 3, the ratio (a(n+1) + a(n-1)) / a(n) is constant.
  have h_ratio : ∀ n ≥ 3, (a (n + 1) + a (n - 1)) / a (n) = (a (n) + a (n - 2)) / a (n - 1) := by
    intro n hn
    suffices h0 : ∀ n ≥ 3, (a (n + 1) + a (n - 1)) / a (n) - (a (n) + a (n - 2)) / a (n - 1) = 0 from eq_of_sub_eq_zero (h0 n hn)
    intro n hn'
    have hn'' : n - 1 ≥ 2 := by exact Nat.le_sub_of_add_le hn'
    calc
      (a (n + 1) + a (n - 1)) / a (n) - (a (n) + a (n - 2)) / a (n - 1) = (a (n - 1) * (a (n + 1) + a (n - 1)) - a (n) * (a (n) + a (n - 2))) / (a (n) * a (n - 1)) := by
        have h : a (n) * a (n - 1) ≠ 0 := mul_ne_zero (h_ne_zero n (by linarith)) (h_ne_zero (n - 1) (Nat.le_sub_of_add_le hn'))
        field_simp [h]
        ring_nf
        have h1 : ∀ n ≥ 2, a n * (a n)⁻¹ = 1 := by
          intro n hn
          exact Field.mul_inv_cancel (a (n)) (h_ne_zero n (by linarith))
        have h2 : a (1 + n) * a (n - 1) * a n * (a n)⁻¹ = a (1 + n) * a (n - 1) := by
          rw [mul_assoc, h1, mul_one]; linarith
        have h3 : - (a (n - 1) * a n * a (n - 2) * (a (n - 1))⁻¹) = - a n * a (n - 2) := by
          calc
            - (a (n - 1) * a n * a (n - 2) * (a (n - 1))⁻¹) = - a n * a (n - 2) * ( a (n - 1) * (a (n - 1))⁻¹) := by ring
            _ = - a n * a (n - 2) * 1:= by 
              rw [h1]
              exact hn''
            _ = - a n * a (n - 2) := by ring
        have h4 : - a (n - 1) * a n ^ 2 * (a (n - 1))⁻¹ = - a n ^ 2 := by 
          calc
            - a (n - 1) * a n ^ 2 * (a (n - 1))⁻¹ = - a n ^ 2 * a (n - 1) * (a (n - 1))⁻¹ := by ring
            _ = - a n ^ 2 * (a (n - 1) * (a (n - 1))⁻¹) := by rw [mul_assoc]
            _ = - a n ^ 2 * 1 := by 
              rw [h1]
              exact hn''
            _ = - a n ^ 2 := by rw [mul_one]
        have h5 : a (n - 1) ^ 2 * a n * (a n)⁻¹ = a (n - 1) ^ 2 := by rw [mul_assoc, h1, mul_one]; linarith
        rw [h2, h3]
        have h6 : a (1 + n) * a (n - 1) + (-a n * a (n - 2) - a (n - 1) * a n ^ 2 * (a (n - 1))⁻¹) + a (n - 1) ^ 2 * a n * (a n)⁻¹ = a (1 + n) * a (n - 1) + (-a n * a (n - 2)) + (- a (n - 1) * a n ^ 2 * (a (n - 1))⁻¹) + a (n - 1) ^ 2 * a n * (a n)⁻¹ := by
          ring
        rw [h6, h4, h5] 
        ring
      _ = ((a (n + 1) * a (n - 1)) - a (n) ^ 2 + a (n - 1) ^ 2 - a (n) * a (n - 2)) / (a (n) * a (n - 1)) := by ring
      _ = (2007 + a (n) ^ 2 - a (n) ^ 2 + a (n - 1) ^ 2 - a (n) * a (n - 2)) / (a (n) * a (n - 1)) := by
        have hn'': n ≥ 2 := by linarith
        rw [han n (hn'')]
        ring
      _ = (2007 + a (n - 1) ^ 2 - a (n) * a (n - 2)) / (a (n) * a (n - 1)) := by ring
      _ = (2007 + a (n - 1) ^ 2 - a (n - 1 + 1) * a (n - 1 - 1)) / (a (n) * a (n - 1)) := by
        suffices h0 : a (n) = a (n - 1 + 1)  ∧ a (n - 2) = a (n - 1 - 1) from by rw[h0.1, h0.2]
        constructor
        congr
        cases' n with n'
        · simp [Nat.zero_sub]
          linarith
        · simp [Nat.succ_sub, Nat.succ_eq_add_one]
        have h : n - 2 = n - 1 - 1 := by
          calc n - 2 = n - (1 + 1) := by rfl
                   _ = n - 1 - 1 := by rw [Nat.sub_sub]
        rw [h]

      _ = (2007 + a (n - 1) ^ 2 - (a (n - 1) ^ 2 + 2007)) / (a (n) * a (n - 1)) := by
        have hn'''(hn : n ≥ 3) : n - 1 ≥ 2 := by exact Nat.le_sub_one_of_lt hn'
        rw [han (n - 1) (hn''' hn')]
      _ = 0 / (a (n) * a (n - 1)) := by ring
      _ = 0 := by simp

  -- We prove that the ratio (a(n+1) + a(n-1)) / a(n) is equal to 225 for all n ≥ 2.
  have h_ratio_eq_225 : ∀ n ≥ 2 , (a (n + 1) + a (n - 1)) / a (n) = 225 := by 
    intro n hn
    induction' n using Nat.strong_induction_on with n ih
    cases' Nat.eq_or_lt_of_le hn with h2 h2
    rw [← h2]
    calc
      (a (2 + 1) + a (2 - 1)) / a 2 = (a 3 + a 1) / a 2 := by rfl
      _ = (672 + 3) / 3 := by rw [ha1, ha2, h_a3]
      _ = 225 := by norm_num
    have n_pos : 0 < n := by linarith
    have hn_minus_1 : n - 1 ≥ 2 := by exact Nat.le_sub_one_of_lt h2
    have hn_minus_1_lt_n : n - 1 < n := by apply Nat.pred_lt_self n_pos
    have hn_ge_3 : n ≥ 3 := Nat.succ_le_of_lt h2
    have IH : (a (n) + a (n - 2)) / a (n - 1) = 225 := by
      have h1 : a (n) = a (n - 1 + 1) := by 
        cases' n with n'
        · simp [Nat.zero_sub]
          linarith
        · simp [Nat.succ_sub, Nat.succ_eq_add_one]
      have h2 : a (n - 2) = a (n - 1 - 1) := by
        have h2' : n - 2 = n - 1 - 1 := by 
          calc
             n - 2 = n - (1 + 1) := by rfl
                 _ = n - 1 - 1 := by rw [Nat.sub_sub]
        rw [h2']
      rw [h1,h2]
      apply ih (n - 1) 
      · exact hn_minus_1_lt_n
      · exact hn_minus_1
    rw [← IH]
    exact h_ratio n hn_ge_3
     
  -- We derive a recurrence relation: a(n+1) = 225 * a(n) - a(n-1) for n ≥ 2.
  have h_recur : ∀ n ≥ 2 , a (n + 1) = 225 * a (n) - a (n - 1) := by 
    intro n hn
    suffices h0 : ∀ n ≥ 2 , a (n + 1) + a (n - 1) = 225 * a (n) from by exact eq_sub_of_add_eq (h0 n hn)
    intro n' hn'
    rw [← h_ratio_eq_225 n' hn']
    field_simp [h_ne_zero]

  -- We show that for n ≥ 2, (a(n)^2 + a(n-1)^2) / (a(n) * a(n-1)) = 225 - 2007 / (a(n) * a(n-1)).
  have h_eq : ∀ n ≥ 2 , (a (n) ^ 2 + a (n - 1) ^ 2) / (a (n) * a (n - 1)) = 225 - 2007 / (a (n) * a (n - 1)) := by
    intro n hn 
    have h : a (n) * a (n - 1) ≠ 0 := by
      cases' Nat.eq_or_lt_of_le hn with h2 h2
      rw [← h2]
      calc
        a (2) * a (2 - 1) = a (2) * a (1) := by rfl
        _ = 3 * 3 := by rw [ha1, ha2]
        _ ≠ 0 := by norm_num
      have hn_ge_3 : n ≥ 3 := Nat.succ_le_of_lt h2
      exact mul_ne_zero (h_ne_zero n (by linarith)) (h_ne_zero (n - 1) (Nat.le_sub_of_add_le hn_ge_3))
  
    suffices h1 : ∀ n ≥ 2 , a (n) ^ 2 + a (n - 1) ^ 2 = 225 * (a (n) * a (n - 1)) - 2007 from by field_simp [h1]
    intro n' hn'
    rw [← h_ratio_eq_225 n' hn']
    field_simp [h_ne_zero]
    suffices h2 : (a (n' + 1) + a (n' - 1)) * a (n' - 1) - 2007 = a n' ^ 2 + a (n' - 1) ^ 2  from by rw [← h2]; ring
    calc
      (a (n' + 1) + a (n' - 1)) * a (n' - 1) - 2007 = a (n' + 1) * a (n' - 1) + a (n' - 1) ^ 2 - 2007 := by ring
      _ = a (n') ^ 2 + 2007 + a (n' - 1) ^ 2 - 2007 := by rw [(han n' hn')]
      _ = a (n') ^ 2 + a (n' - 1) ^ 2 := by ring

  -- We show that the sequence is strictly increasing for n ≥ 3.
  have h_incr : ∀ n ≥ 3 , a (n) > a (n-1) := by 
    intro n hn
    induction' n using Nat.strong_induction_on with n ih
    have h1 : a (n) = a (n - 1 + 1) := by 
      cases' n with n'
      · simp [Nat.zero_sub]
        linarith
      · simp [Nat.succ_sub, Nat.succ_eq_add_one]
    have h2 : a (n - 2) = a (n - 1 - 1) := by
        have h2' : n - 2 = n - 1 - 1 := by 
          calc
             n - 2 = n - (1 + 1) := by rfl
                 _ = n - 1 - 1 := by rw [Nat.sub_sub]
        rw [h2']
    have n_pos : 0 < n := by linarith
    have hn_minus_1 : n - 1 ≥ 2 := by exact Nat.le_sub_one_of_lt hn
    have hn_minus_1_lt_n : n - 1 < n := by apply Nat.pred_lt_self n_pos
    cases' Nat.eq_or_lt_of_le hn with h3 h3
    · rw [← h3]
      calc
        a 3 = 672 := by rw [h_a3]
          _ > 3 := by norm_num
          _ = a 2 := by rw [← ha2]
          _ = a (3 - 1) := by 
            have h : 2 = 3 - 1 := by norm_num
            rw [h]
    have IH : a (n - 1) > a (n - 2) := by
      apply ih (n - 1)   
      · exact hn_minus_1_lt_n
      · exact Nat.le_sub_one_of_lt h3 
    have IH_neg : - a (n - 1) < - a (n - 2) := by
      exact neg_lt_neg IH
    calc
      a (n) = a (n - 1 + 1) := by rw [h1]
          _ = 225 * a (n - 1) - a (n - 1 - 1) := by rw [h_recur (n - 1) hn_minus_1]
          _ = 225 * a (n - 1) - a (n - 2) := by rw [h2]
          _ > 225 * a (n - 1) - a (n - 1) := by exact add_lt_add_left IH_neg (225 * a (n - 1))
          _ = 224 * a (n - 1) := by ring
          _ > a (n - 1) := by 
            suffices h : 224 * a (n - 1) - a (n - 1) > 0 from by exact sub_pos.mp h
            calc 
              224 * a (n - 1) - a (n - 1) = 223 * a (n - 1) := by ring
              _  > 0 := by exact mul_pos (by linarith) (by exact h_pos (n - 1) (by linarith))

  -- Prove that for n ≥ 4, a(n) > 2007
  have h_incr_2007 : ∀ n ≥ 4 , a (n) > 2007 := by 
    intro n hn
    induction' n using Nat.strong_induction_on with n ih
    cases' Nat.eq_or_lt_of_le hn with h4 h4
    rw [← h4]
    calc
      a (4) = a (4 - 1 + 1) := by 
        have h : 4 = 4 - 1 + 1 := by ring
        rw [h]
          _ = 225 * a (4 - 1) - a (4 - 1 - 1) := by rw [h_recur (4 - 1) (by linarith)]
          _ = 225 * a (3) - a (2) := by
            have h : 4 - 1 = 3 ∧ 4 - 1 - 1 = 2 := by
              constructor
              norm_num
              norm_num
            rw [h.1,h.2]
          _ = 225 * 672 - 3 := by rw [ha2, h_a3]  
          _ > 2007 := by norm_num
    have IH : a (n - 1) > 2007 := by 
      have n_pos : 0 < n := by linarith
      have hn_minus_1 : n - 1 ≥ 4 := by exact Nat.le_sub_one_of_lt h4
      have hn_minus_1_lt_n : n - 1 < n := by apply Nat.pred_lt_self n_pos
      apply ih (n - 1)
      · exact hn_minus_1_lt_n
      · exact hn_minus_1
    calc
      a n > a (n - 1) := by exact h_incr n (by linarith)
        _ > 2007 := by exact IH
     
  -- Specialize the identity for n = 2007.
  have h_eq_2007 : (a 2007 ^ 2 + a 2006 ^ 2) / (a 2007 * a 2006) = 225 - 2007 / (a 2007 * a 2006) := by exact h_eq 2007 (by norm_num)

  -- Show that the expression is less than 224 + 1.
  have h_final : (a 2007 ^ 2 + a 2006 ^ 2) / (a 2007 * a 2006) < (224 : ℝ) + 1 := by
    rw [h_eq_2007]
    norm_num
    refine mul_pos (h_pos 2007 (by norm_num)) ?_
    exact h_pos 2006 (by norm_num)

  -- Show that the expression is greater than or equal to 224.
  have h_final2 : (a 2007 ^ 2 + a 2006 ^ 2) / (a 2007 * a 2006) ≥ (224 : ℝ) := by
    rw [h_eq_2007]
    have h1 : a 2007 * a 2006 > 2007 * 2007 := by
     apply mul_lt_mul''
     · exact h_incr_2007 2007 (by norm_num)
     · exact h_incr_2007 2006 (by norm_num)
     · exact (by norm_num : (2007 : ℝ) ≥ 0)
     · exact (by norm_num : (2007 : ℝ) ≥ 0)
    have h_pos1 : 0 < a 2007 * a 2006 := by
      exact mul_pos (h_pos 2007 (by norm_num)) (h_pos 2006 (by norm_num))
    have h_pos2_real : (0 : ℝ) < ↑(2007 * 2007) := by norm_num
    have h2 : (2007 : ℝ) > 0 := by norm_num
    have h3 : 1/(a 2007 * a 2006) ≤ 1/(2007 * 2007) := by exact (one_div_le_one_div h_pos1 h_pos2_real).mpr (le_of_lt (LT.lt.gt h1))
    have h4 : (a 2007 * a 2006) ⁻¹ ≤ (2007 * 2007) ⁻¹ := by simpa [one_div,one_div] using h3
    have h5 : 0 < (a 2007 * a 2006)⁻¹ := by exact inv_pos_of_pos h_pos1
    have h6 : 2007 / (a (2007) * a (2006)) < 1 := by
      calc
        2007 / (a (2007) * a (2006)) ≤ 2007 / (2007 * 2007) := by exact mul_le_mul (by norm_num) h4 (le_of_lt h5) (le_of_lt (by norm_num))
        _ = 1 / 2007 := by norm_num
        _ < 1 := by norm_num
    linarith

  -- Conclude that the floor of the expression is 224.
  show ⌊(a 2007 ^ 2 + a 2006 ^ 2) / (a 2007 * a 2006)⌋ = 224
  apply Int.floor_eq_iff.2
  constructor
  · exact h_final2
  · exact h_final