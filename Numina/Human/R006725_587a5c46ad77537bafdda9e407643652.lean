import Mathlib
open Finset Set Nat
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
noncomputable section

/-Let $a,b,c,d$ be positive integer side lengths of a quadrilateral. Suppose that for each side $s \in \{a,b,c,d\}$, the sum of the other three sides, $T_s$, is an integer multiple of $s$, and furthermore $T_s \ge 3s$. Prove that all four sides $a,b,c,d$ must be of equal length.-/
theorem number_theory_6010101
  (a b c d : ℕ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0)
  (h_Ta : ∃ ka : ℕ, ka ≥ 3 ∧ b + c + d = ka * a)
  (h_Tb : ∃ kb : ℕ, kb ≥ 3 ∧ a + c + d = kb * b)
  (h_Tc : ∃ kc : ℕ, kc ≥ 3 ∧ a + b + d = kc * c)
  (h_Td : ∃ kd : ℕ, kd ≥ 3 ∧ a + b + c = kd * d) :
  a = b ∧ a = c ∧ a = d := by
  obtain ⟨ka, h_ka_ge3, h_Ta_eq⟩ := h_Ta
  obtain ⟨kb, h_kb_ge3, h_Tb_eq⟩ := h_Tb
  obtain ⟨kc, h_kc_ge3, h_Tc_eq⟩ := h_Tc
  obtain ⟨kd, h_kd_ge3, h_Td_eq⟩ := h_Td
  have h_eq_ab : a = b := by
    -- Prove that $a = b$ using the given conditions.
    have h_sum_eq : (ka + 1 : ℕ) * a = (kb + 1 : ℕ) * b := by
      -- Prove that $(ka + 1) * a = (kb + 1) * b$.
      have h_sum_a : (ka + 1 : ℕ) * a = a + b + c + d := by
        -- Prove that $(ka + 1) * a = a + b + c + d$.
        nlinarith [h_Ta_eq]
      have h_sum_b : (kb + 1 : ℕ) * b = a + b + c + d := by
        -- Prove that $(kb + 1) * b = a + b + c + d$.
        nlinarith [h_Tb_eq]
      -- Combine the results to get $(ka + 1) * a = (kb + 1) * b$.
      linarith
    -- Prove that $a = b$ using the fact that $(ka + 1) * a = (kb + 1) * b$.
    have h_a_le_b : a ≤ b := by
      by_contra h
      have h_a_gt_b : a > b := by omega
      have h_contra_ab : (ka + 1 : ℕ) * a > (kb + 1 : ℕ) * b := by
        nlinarith [h_ka_ge3, h_kb_ge3]
      omega
    have h_b_le_a : b ≤ a := by
      by_contra h
      have h_b_gt_a : b > a := by omega
      have h_contra_ba : (kb + 1 : ℕ) * b > (ka + 1 : ℕ) * a := by
        nlinarith [h_ka_ge3, h_kb_ge3]
      omega
    linarith
  have h_eq_ac : a = c := by
    -- Prove that $a = c$ using the given conditions.
    have h_sum_eq : (ka + 1 : ℕ) * a = (kc + 1 : ℕ) * c := by
      -- Prove that (ka + 1) * a = (kc + 1) * c.
      have h_sum_a : (ka + 1 : ℕ) * a = a + b + c + d := by
        -- Prove that $(ka + 1) * a = a + b + c + d$.
        nlinarith [h_Ta_eq]
      have h_sum_c : (kc + 1 : ℕ) * c = a + b + c + d := by
        -- Prove that $(kc + 1) * c = a + b + c + d$.
        nlinarith [h_Tc_eq]
      -- Combine the results to get $(ka + 1) * a = (kc + 1) * c$.
      linarith
    -- Prove that $a = c$ using the fact that $(ka + 1) * a = (kc + 1) * c$.
    have h_a_le_c : a ≤ c := by
      by_contra h
      have h_a_gt_c : a > c := by omega
      have h_contra_ac : (ka + 1 : ℕ) * a > (kc + 1 : ℕ) * c := by
        nlinarith [h_ka_ge3, h_kc_ge3]
      omega
    have h_c_le_a : c ≤ a := by
      by_contra h
      have h_c_gt_a : c > a := by omega
      have h_contra_ca : (kc + 1 : ℕ) * c > (ka + 1 : ℕ) * a := by
        nlinarith [h_ka_ge3, h_kc_ge3]
      omega
    linarith
  have h_eq_ad : a = d := by
    -- Prove that $a = d$ using the given conditions.
    have h_sum_eq : (ka + 1 : ℕ) * a = (kd + 1 : ℕ) * d := by
      -- Prove that (ka + 1) * a = (kd + 1) * d.
      have h_sum_a : (ka + 1 : ℕ) * a = a + b + c + d := by
        -- Prove that $(ka + 1) * a = a + b + c + d$.
        nlinarith [h_Ta_eq]
      have h_sum_d : (kd + 1 : ℕ) * d = a + b + c + d := by
        -- Prove that $(kd + 1) * d = a + b + c + d$.
        nlinarith [h_Td_eq]
      -- Combine the results to get $(ka + 1) * a = (kd + 1) * d$.
      linarith
    -- Prove that $a = d$ using the fact that $(ka + 1) * a = (kd + 1) * d$.
    have h_a_le_d : a ≤ d := by
      by_contra h
      have h_a_gt_d : a > d := by omega
      have h_contra_ad : (ka + 1 : ℕ) * a > (kd + 1 : ℕ) * d := by
        nlinarith [h_ka_ge3, h_kd_ge3]
      omega
    have h_d_le_a : d ≤ a := by
      by_contra h
      have h_d_gt_a : d > a := by omega
      have h_contra_da : (kd + 1 : ℕ) * d > (ka + 1 : ℕ) * a := by
        nlinarith [h_ka_ge3, h_kd_ge3]
      omega
    linarith
  -- Combine those result.
  exact ⟨h_eq_ab, h_eq_ac, h_eq_ad⟩
