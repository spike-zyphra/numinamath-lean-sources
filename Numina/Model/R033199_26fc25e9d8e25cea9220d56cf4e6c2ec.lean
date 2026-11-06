import Mathlib

theorem algebra_11668 (m : ℝ) (f : ℝ → ℝ) (hf : f = fun x => m * x ^ 2 - 2 * x + 1)
    (h : ∃! x, x > 0 ∧ f x = 0) :
    m ≤ 0 ∨ m = 1 := by
  rcases h with ⟨x, hx_pos, hx_neg⟩
  simp [hf] at hx_pos

  have hfx : m * x ^ 2 - 2 * x + 1 = 0 := by
    linarith [hx_pos.2]

  have hf_eq : ∀ y, y > 0 ∧ f y = 0 → y = x := by 
    intro y hy 
    simpa using hx_neg y hy

  by_cases h1 : m > 0
  · -- Case where m > 0: We need to prove m ≤ 0 ∨ m = 1, which will be m = 1
    have hm_eq_1 : m = 1 := by 
      by_contra hneq1 
      push_neg at hneq1
      have hmp : 0 < m := by linarith 
      have hy_pos : (1 / (m * x) : ℝ) > 0 := by
        apply div_pos 
        · linarith 
        · -- Show m * x > 0
          have hx1 : x > 0 := hx_pos.1 
          nlinarith [show m > 0 by linarith, hx1]
      have hy_eq0 : f (1 / (m * x)) = 0 := by 
        simp [hf]
        have hx1 : x > 0 := hx_pos.1 
        have eq1 : m * x ^ 2 - 2 * x + 1 = 0 := hfx 
        field_simp [show m * x ≠ 0 by 
          nlinarith [show m > 0 by linarith, hx_pos.1]
        ] at *
        <;> nlinarith [sq_nonneg (x), sq_nonneg (m - 1), sq_nonneg (x * m - 1)]
      have hy_ne_x : (1 / (m * x) : ℝ) ≠ x := by 
        by_contra heq 
        have hx1 : x > 0 := hx_pos.1 
        have eq1 : m * x ^ 2 = 1 := by 
          field_simp [show m ≠ 0 by nlinarith, show x ≠ 0 by nlinarith] at heq ⊢
          <;> nlinarith [heq, hfx, show 0 < m by linarith, hx1]
        have eq2 : m * x ^ 2 - 2 * x + 1 = 0 := hfx 
        have eq3 : x = 1 := by 
          nlinarith [eq1, hfx, show 0 < m by linarith, hx1]
        have eq4 : m = 1 := by 
          rw [show x = 1 by linarith [eq3]] at hfx
          nlinarith 
        contradiction
      have h1_eq : (1 / (m * x) : ℝ) = x := hf_eq (1 / (m * x)) ⟨hy_pos, hy_eq0⟩
      rw [h1_eq] at hy_ne_x 
      all_goals contradiction 
    simp [hm_eq_1]
    all_goals linarith 
  · -- Case where m ≤ 0: We need to prove m ≤ 0 ∨ m = 1
    have : m ≤ 0 := by linarith 
    left 
    linarith