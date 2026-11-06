import Mathlib

theorem number_theory_172736 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 2 * a + 1 ∣ 3 * b - 1) (h2 : 2 * b + 1 ∣ 3 * a - 1) :
    (a, b) = (2, 2) ∨ (a, b) = (12, 17) ∨ (a, b) = (17, 12) := by 
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  have cdeq : (3 * b - 1) * (3 * a - 1) = c * d * (2 * a + 1) * (2 * b + 1) := by 
    rw [hc, hd]
    ring
  have ineq1 : (2 * a + 1) * (3 / (2 : ℝ)) ≥  (3 * a - 1):= by
    field_simp
    refine (le_div_iff₀ ?_).mpr ?_
    positivity
    norm_cast
    linarith
  have ineq2 : (2 * b + 1) * (3 / (2:ℝ)) ≥ (3 * b - 1) := by
    field_simp
    refine (le_div_iff₀ ?_).mpr ?_
    positivity
    norm_cast
    linarith
  have ineq3 : (2 * a + 1) * (2 * b + 1) * 3 > (3 * b - 1) * (3 * a - 1) := by
    nlinarith
  norm_cast at ineq3
  rw [cdeq] at ineq3
  have pos : 0 < (2 * a + 1) * (2 * b + 1) := mul_pos (by linarith) (by linarith)
  have cdle : c * d < 3 := by nlinarith
  have cpos : c > 0 := by nlinarith
  have cdpos : d > 0 := by nlinarith
  have cle : c ≤ 2 := by nlinarith
  have dle: d ≤ 2 := by nlinarith
  interval_cases c
  -- cases c = 1
  -- cases d = 1
  interval_cases d
  simp_all
  have aeq : a = 2 := by nlinarith
  have beq : b = 2 := by linarith
  left 
  exact ⟨aeq, beq⟩
  simp_all
  have aeq : a = 17 := by 
    nlinarith
  have beq : b = 12 := by linarith
  right
  right
  exact ⟨aeq, beq⟩
  interval_cases d
  simp_all
  have aeq : a = 12 := by nlinarith
  have beq : b = 17 := by linarith
  right
  left
  exact ⟨aeq, beq⟩
  linarith