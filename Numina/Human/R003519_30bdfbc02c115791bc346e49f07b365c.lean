import Mathlib

theorem algebra_190047 (a : ℝ) (ha : a ≠ 5) (h : ∃ x : ℝ, x < 0 ∧ (5 : ℝ)^x = (a + 3) / (5 - a)) :
    a ∈ Set.Ioo (-3) 1 := by 
  obtain ⟨x, hx, heq⟩ := h
  have ineq1 : (5 : ℝ) ^ x < 1 := by 
    refine Real.rpow_lt_one_of_one_lt_of_neg ?_ hx
    linarith
  have ineq2 : (5 : ℝ) ^ x > 0 := by 
    positivity
  have ineq3 : (a + 3) / (5 - a) < 1 := by 
    linarith
  have ineq4 : (a + 3) / (5 - a) > 0 := by 
    linarith
  have ineq5 : (a + 3) / (5 - a) - 1 < 0 := by 
    linarith
  have neq : 5 - a ≠ 0 := by 
    by_contra hc
    have aeq : a = 5 := by linarith
    exact ha aeq
  have eq1 : (a + 3) / (5 - a) - 1 = (2 * a - 2) / (5 - a) := by 
    field_simp
    ring
  rw [eq1] at ineq5
  -- (2 * a - 2) / (5 - a) < 0
  -- 0 < 2 * a - 2 ∧ 5 - a < 0 ∨ 2 * a - 2 < 0 ∧ 0 < 5 - a
  obtain hneg := div_neg_iff.mp ineq5
  -- (a + 3) / (5 - a) > 0
  -- 0 < a + 3 ∧ 0 < 5 - a ∨ a + 3 < 0 ∧ 5 - a < 0
  obtain hpos := div_pos_iff.mp ineq4
  obtain ⟨h1, h2⟩| ⟨h1, h2⟩ := hneg
  have agt : a > 1 := by linarith
  have agt' : a > 5 := by linarith
  obtain ⟨h1', h2'⟩| ⟨h1', h2'⟩ := hpos
  have alt : a < 5 := by linarith
  linarith
  have alt : a < -3 := by linarith
  linarith
  have alt : a < 1 := by linarith
  have alt' : a < 5 := by linarith
  obtain ⟨h1', h2'⟩| ⟨h1', h2'⟩ := hpos
  have agt : a > -3 := by linarith
  simp
  exact ⟨agt, alt⟩
  have agt : a > 5 := by linarith
  linarith