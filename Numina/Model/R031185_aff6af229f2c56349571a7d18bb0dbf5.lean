import Mathlib

theorem algebra_209111 (p : ℝ) :
    (∃! xy : ℝ × ℝ, let x := xy.1 ; let y := xy.2 ;
     x^2 - y^2 = 0 ∧ x * y + p * x - p * y = p^2) ↔ p = 0 := by 
  constructor 
  · -- Forward: if there's a unique solution, then p = 0.
    intro h
    rcases h with ⟨⟨x, y⟩, h1, h2⟩ 
    have eq1 : x ^ 2 - y ^ 2 = 0 := h1.1 
    have eq2 : x * y + p * x - p * y = p ^ 2 := h1.2 
    have hy_eq : y = x ∨ y = -x := by 
      have h : x ^ 2 = y ^ 2 := by linarith 
      have : x = y ∨ x = -y := by 
        apply sq_eq_sq_iff_eq_or_eq_neg.mp 
        linarith 
      cases this with 
      | inl h_eq => 
        left 
        linarith 
      | inr h_eq => 
        right 
        linarith 
    cases hy_eq with 
    | inl hyx => 
      rw [show y = x by linarith [hyx]] at eq2 
      have eq3 : x ^ 2 = p ^ 2 := by 
        nlinarith 
      have hx_eq_p_or_neg_p : x = p ∨ x = -p := by 
        have h : x ^ 2 = p ^ 2 := eq3 
        have : x = p ∨ x = -p := by 
          have h' : x ^ 2 - p ^ 2 = 0 := by linarith 
          have h'' : (x - p) * (x + p) = 0 := by 
            nlinarith 
          cases (mul_eq_zero.mp h'') with 
          | inl h_eq_zero => 
            left; linarith 
          | inr h_eq_zero => 
            right; linarith 
        assumption 
      cases hx_eq_p_or_neg_p with 
      | inl hx_eq_p => 
        -- Subcase 1a: x = p, y = x
        have hx : x = p := hx_eq_p
        have hy : y = p := by 
          rw [show y = x by linarith [hyx]]
          all_goals linarith 
        -- Assume (p, -p) is another solution.
        have h_eq5 : (p, -p) = (x, y) := by 
          apply h2 
          -- Verify (p, -p) is a solution
          constructor 
          · -- First equation: x^2 - y^2 = 0.
            ring_nf 
          · -- Second equation: x * y + p * x - p * y = p^2.
            ring_nf 
        rw [show (x, y) = (p, p) by simp [hx, hy]] at h_eq5 
        have eq6 : p = 0 := by 
          simp [Prod.ext_iff] at h_eq5 
          all_goals nlinarith 
        linarith 
      | inr hx_eq_neg_p => 
        -- Subcase 1b: x = -p, y = x
        have hx : x = -p := hx_eq_neg_p
        have hy : y = -p := by 
          rw [show y = x by linarith [hyx]]
          all_goals linarith 
        -- Assume (p, -p) is another solution.
        have h_eq6 : (p, -p) = (x, y) := by 
          apply h2 
          -- Verify (p, -p) is a solution.
          constructor 
          · -- First equation: x^2 - y^2 = 0.
            ring_nf 
          · -- Second equation: x * y + p * x - p * y = p^2.
            ring_nf 
        rw [show (x, y) = (-p, -p) by simp [hx, hy]] at h_eq6 
        have eq7 : p = 0 := by 
          simp [Prod.ext_iff] at h_eq6 
          all_goals nlinarith 
        linarith 
    | inr hy_neg_x => 
      rw [show y = -x by linarith [hy_neg_x]] at eq2 
      have eq3 : x = p := by 
        nlinarith 
      have hx : x = p := eq3 
      have hy : y = -p := by 
        rw [show y = -x by linarith [hy_neg_x]]
        all_goals linarith 
      -- Assume (p, p) is another solution.
      have h_eq5 : (p, p) = (x, y) := by 
        apply h2 
        -- Verify (p, p) is a solution.
        constructor 
        · -- First equation: x^2 - y^2 = 0.
          ring_nf 
        · -- Second equation: x * y + p * x - p * y = p^2.
          ring_nf 
      rw [show (x, y) = (p, -p) by simp [hx, hy]] at h_eq5 
      have eq7 : p = 0 := by 
        simp [Prod.ext_iff] at h_eq5 
        all_goals nlinarith 
      linarith 
  · -- Backward: if p = 0, then there's a unique solution.
    intro h_eq5 
    rw [h_eq5] 
    use (0, 0)
    constructor 
    · -- Show (0, 0) is a solution 
      simp 
    · -- Show any solution equals (0, 0)
      intro s h1 
      rcases h1 with ⟨hk_eq, hk_eq2⟩ 
      have eq3 : s.1 ^ 2 = s.2 ^ 2 := by linarith 
      have eq4 : s.1 * s.2 = 0 := by 
        nlinarith 
      have h_eq6 : s.1 = 0 := by 
        cases (mul_eq_zero.mp eq4) with 
        | inl h1_eq_zero => 
          have h_eq7 : s.1 = 0 := by 
            linarith 
          exact h_eq7 
        | inr h2_eq_zero => 
          -- Case where s.2 = 0.
          have h_eq8 : s.2 = 0 := by 
            linarith 
          have h_eq9 : s.1 ^ 2 = 0 := by 
            nlinarith 
          have h_eq10 : s.1 = 0 := by 
            nlinarith 
          exact h_eq10 
      have h_eq7 : s.2 = 0 := by 
        rw [h_eq6] at eq3 
        nlinarith 
      simp [Prod.ext_iff, h_eq6, h_eq7]