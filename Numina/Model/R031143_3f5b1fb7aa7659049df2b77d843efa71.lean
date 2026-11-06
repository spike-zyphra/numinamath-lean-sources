import Mathlib

open Real

theorem inequalities_292914 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : n ≤ x) :
    x + n / x ≥ n + 1 ∧ (x + n / x = n + 1 ↔ x = n) := by
  have hn' : (n : ℝ) > (0 : ℝ) := by
    exact_mod_cast (show (n : ℕ) > 0 by linarith)
  have hx1 : (n : ℝ) ≤ x := by
    exact_mod_cast hx
  constructor 
  · -- Show that x + n / x ≥ n + 1
    have h1 : x + (n : ℝ) / x ≥ (n : ℝ) + 1 := by 
      have hx2 : x > (0 : ℝ) := by
        nlinarith [hx1, hn']
      have h2 : x + (n : ℝ) / x - ((n : ℝ) + 1 : ℝ) ≥ 0 := by 
        have h3 : x + (n : ℝ) / x - ((n : ℝ) + 1 : ℝ) = (x ^ 2 + (n : ℝ) - ((n : ℝ) + 1) * x) / x := by 
          field_simp 
          <;> ring 
        rw [h3]
        have h5 : x ^ 2 + (n : ℝ) - ((n : ℝ) + 1) * x ≥ 0 := by 
          have hx6 : x ≥ (n : ℝ) := by 
            exact_mod_cast (show n ≤ x by linarith [hx])
          have hn9 : (n : ℝ) ≥ (1 : ℝ) := by
            have h10 : n ≥ 1 := by 
              omega 
            exact_mod_cast h10 
          nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x - 1), sq_nonneg (x - (n : ℝ)), sq_nonneg (x - 1)]
        apply div_nonneg 
        linarith 
        all_goals linarith 
      linarith 
    norm_num at h1 ⊢
    nlinarith 
  · -- Show that equality holds if and only if x = n 
    constructor 
    · -- If x + n / x = n + 1 then x = n 
      intro h_eq 
      have hx2 : x > (0 : ℝ) := by 
        have hn' : (n : ℝ) > (0 : ℝ) := by 
          exact_mod_cast (show (n : ℕ) > 0 by linarith) 
        have hx1 : (n : ℝ) ≤ x := by 
          exact_mod_cast hx 
        nlinarith 
      have h_eq1 : (x ^ 2 + (n : ℝ) - ((n : ℝ) + 1) * x) / x = 0 := by 
        have h_eq1 : x + (n : ℝ) / x = (n : ℝ) + 1 := by 
          linarith [h_eq] 
        have h_eq2 : x + (n : ℝ) / x - ((n : ℝ) + 1) = 0 := by 
          linarith 
        have h_eq3 : (x ^ 2 + (n : ℝ) - ((n : ℝ) + 1) * x) / x = x + (n : ℝ) / x - ((n : ℝ) + 1) := by 
          field_simp 
          <;>  ring 
        rw [h_eq3] 
        linarith 
      have h_eq2 : x ^ 2 + (n : ℝ) - ((n : ℝ) + 1) * x = 0 := by 
        have h_eq2 : (x ^ 2 + (n : ℝ) - ((n : ℝ) + 1) * x) / x = 0 := by 
          linarith [h_eq1]
        have hx2 : x > 0 := by 
          nlinarith [hx1]
        field_simp at h_eq2 
        nlinarith 
      have h_eq3 : (x - 1) * (x - (n : ℝ)) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.mp h_eq3) with
      | inl h6 => 
        -- x - 1 = 0, so x = 1 
        have h1_eq : x = 1 := by linarith 
        -- From hx: n ≤ x, we have ↑n ≤ 1 
        have h2_le : (n : ℝ) ≤ (1 : ℝ) := by
          have hx1_sub : (n : ℝ) ≤ (x : ℝ) := by 
            exact_mod_cast hx 
          rw [h1_eq] at hx1_sub 
          linarith 
        have hn1 : n = 1 := by
          have hn2 : (n : ℝ) > (0 : ℝ) := hn' 
          have hn3 : (n : ℝ) ≤ (1 : ℝ) := h2_le 
          have hn6 : n > 0 := by 
            exact_mod_cast (show 0 < n by linarith) 
          have hn7 : n ≤ 1 := by 
            by_contra h 
            push_neg at h 
            have hn8 : n ≥ 2 := by omega 
            have hn9 : (n : ℝ) ≥ (2 : ℝ) := by 
              exact_mod_cast hn8 
            nlinarith 
          have : n = 1 := by omega 
          assumption 
        have hx_eqn : x = (n : ℝ) := by
          rw [h1_eq, show (n : ℝ) = (1 : ℝ) by exact_mod_cast hn1] 
          all_goals norm_num
        exact_mod_cast hx_eqn 
      | inr h6 => 
        -- x - n = 0, so x = n 
        have hx_eqn : x = (n : ℝ) := by 
          linarith 
        exact_mod_cast hx_eqn 
    · -- Show that if x = n then x + n / x = n + 1 
      intro h_eq
      have hn' : (n : ℝ) > (0 : ℝ) := by 
        exact_mod_cast (show (0 : ℕ) < n by linarith) 
      have hx4 : x = (n : ℝ) := by 
        exact_mod_cast h_eq 
      rw [hx4] 
      field_simp
      <;> nlinarith