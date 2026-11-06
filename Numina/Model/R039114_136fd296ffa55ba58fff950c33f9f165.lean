import Mathlib

theorem algebra_167928 :
    {(x, y) : ℝ × ℝ | x + y > 0 ∧ (x + y) * 3^(y - x) = 5 / 27 ∧ 3 * Real.logb 5 (x + y) = x - y} = {(4, 1)} := by
  ext ⟨x, y⟩
  simp [-Real.logb_eq_iff_rpow_eq]
  constructor
  · -- Assume ⟨x, y⟩ is in the set.
    rintro ⟨h_pos, h_eq1, h_eq2⟩
    have eq5 : (x + y) * (3 : ℝ) ^ (y - x) = (5 : ℝ) / 27 := h_eq1
    have eq2a : 3 * Real.logb 5 (x + y) = x - y := by
      linarith [h_eq2]
    have eq7 : Real.log ((x + y) * (3 : ℝ) ^ (y - x)) = Real.log (x + y) + (y - x) * Real.log 3 := by
      have h2a : Real.log ((x + y) * (3 : ℝ) ^ (y - x)) = Real.log (x + y) + Real.log ((3 : ℝ) ^ (y - x)) := by
        rw [Real.log_mul (by linarith) (by positivity)]
      have h3a : Real.log ((3 : ℝ) ^ (y - x)) = (y - x) * Real.log 3 := by
        rw [Real.log_rpow]
        all_goals linarith
      have h4a : Real.log ((x + y) * (3 : ℝ) ^ (y - x)) = Real.log (x + y) + (y - x) * Real.log 3 := by
        rw [h2a, h3a]
        all_goals try linarith
      linarith
    have eq8 : Real.log (5 / 27) = Real.log 5 - 3 * Real.log 3 := by
      have h1 : Real.log (5 / 27) = Real.log 5 - Real.log (27 : ℝ) := by
        field_simp [Real.log_div]
      have h2 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
        calc
          Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by norm_num
          _ = 3 * Real.log (3 : ℝ) := by simp [Real.log_pow]
      have h3 : Real.log (5 / 27) = Real.log 5 - 3 * Real.log 3 := by
        rw [h1, h2]
      linarith
    have eq6 : Real.log ((x + y) * (3 : ℝ) ^ (y - x)) = Real.log (5 / 27) := by
      rw [eq5]
    rw [eq7, eq8] at eq6
    have eq3a : Real.logb 5 (x + y) = Real.log (x + y) / Real.log (5 : ℝ) := by
      field_simp [Real.logb]
    rw [eq3a] at eq2a
    have eq4a : Real.log (x + y) = (x - y) / 3 * Real.log 5 := by
      field_simp [(show Real.log (5 : ℝ) ≠ 0 by positivity)] at eq2a ⊢
      nlinarith
    rw [eq4a] at eq6
    have eq5a : (x - y - 3) * Real.log 5 + 3 * (y - x + 3) * Real.log 3 = 0 := by
      nlinarith
    have eq6a : (x - y - 3) * (Real.log 5 - 3 * Real.log 3) = 0 := by
      linarith [eq5a]
    cases' (mul_eq_zero.1 eq6a) with eq7a eq8a
    · -- $x - y - 3 = 0$ case.
      have eq10 : x - y = 3 := by
        linarith
      have eq11 : 3 * Real.logb 5 (x + y) = 3 := by
        linarith [h_eq2, eq10]
      have eq13 : Real.logb 5 (x + y) = 1 := by
        linarith
      have eq14 : x + y = 5 := by
        have h12 : x + y = (5 : ℝ) ^ (1 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq] at eq13
          · linarith
          all_goals nlinarith
        have h13 : (5 : ℝ) ^ (1 : ℝ) = (5 : ℝ) := by
          simp
        linarith [h12, h13]
      have hx : x = 4 := by
        linarith [eq10, eq14]
      have hy : y = 1 := by
        linarith [eq10, eq14]
      simp [hx, hy]
    · -- $\ln(5) - 3 \ln(3) = 0$ case.
      exfalso
      have eq5' : Real.log 5 = 3 * Real.log 3 := by
        linarith
      have h9' : Real.log 5 = 3 * Real.log 3 := by
        linarith [eq5']
      have h10 : Real.log 5 = Real.log (27 : ℝ) := by
        have h11 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
          rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
          simp [Real.log_pow]
        linarith [h9', h11]
      have h12 : (5 : ℝ) = (27 : ℝ) := by
        exact Real.log_injOn_pos (Set.mem_Ioi.mpr (show (5 : ℝ) > 0 by norm_num)) (Set.mem_Ioi.mpr (show (27 : ℝ) > 0 by norm_num)) h10
      all_goals nlinarith
  · -- Show that (4, 1) is a solution.
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    ·
      constructor
      · -- First equation.
        norm_num
      · -- Second equation.
        have h1 : Real.logb 5 (4 + 1 : ℝ) = 1 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith [h1]