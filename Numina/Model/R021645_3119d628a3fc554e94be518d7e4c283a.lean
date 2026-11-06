import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_63761 {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1)
  (h : ∃ a > 0, a ≠ 1 ∧ logb x a + logb y a = 4 * logb (x * y) a) :
  x = y := by
  rcases h with ⟨a, ha_pos, ha_ne_1, heq⟩
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : logb x a = log a / log x := by
    field_simp [logb]
  have h2 : logb y a = log a / log y := by 
    field_simp [logb]
  have h3 : logb (x * y) a = log a / log (x * y) := by
    field_simp [logb]
  rw [h1, h2, h3] at heq
  have h4 : log (x * y) = log x + log y := by 
    rw [log_mul (by linarith) (by linarith)]
  rw [h4] at heq 
  have h5 : log a ≠ 0 := by 
    have ha1 : a > 0 := ha_pos 
    have ha2 : a ≠ 1 := ha_ne_1 
    exact log_ne_zero_of_pos_of_ne_one ha1 ha2
  have hxne : log x ≠ 0 := by 
    have h7 : x > 0 := hx1
    have h8 : x < 1 := hx2
    have h9 : log x < (0 : ℝ) := by 
      have h10 : log x < log (1 : ℝ) := by 
        apply Real.log_lt_log
        linarith 
        linarith 
      have h11 : log (1 : ℝ) = 0 := log_one
      linarith 
    linarith
  have hyne : log y ≠ 0 := by 
    have h7 : y > 0 := hy1
    have h8 : y < 1 := hy2
    have h9 : log y < (0 : ℝ) := by 
      have h10 : log y < log (1 : ℝ) := by 
        apply Real.log_lt_log 
        linarith 
        linarith 
      have h11 : log (1 : ℝ) = 0 := log_one 
      linarith 
    linarith
  have eq5 : log a * (log x + log y) * (log x + log y) = 4 * log a * (log x * log y) := by 
    have eq5a : log a / log x + log a / log y = 4 * (log a / (log x + log y)) := by 
      simpa using heq 
    have h6 : log x * log y ≠ 0 := by 
      apply mul_ne_zero 
      exact hxne 
      exact hyne 
    have h7 : log x + log y ≠ 0 := by 
      have h7 : log x < (0 : ℝ) := by 
        have h10 : log x < log (1 : ℝ) := by 
          apply Real.log_lt_log 
          linarith 
          linarith 
        have h11 : log (1 : ℝ) = 0 := log_one 
        linarith 
      have h8 : log y < (0 : ℝ) := by 
        have h10 : log y < log (1 : ℝ) := by 
          apply Real.log_lt_log 
          linarith 
          linarith 
        have h11 : log (1 : ℝ) = 0 := log_one 
        linarith 
      -- `log x + log y < 0`, thus not `0`.
      have h9 : log x + log y < (0 : ℝ) := by nlinarith 
      linarith 
    have h8' : log a / log x + log a / log y = log a * ((log x + log y) / (log x * log y)) := by 
      field_simp [hxne, hyne]
      <;> ring 
    have eq5b : log a * ((log x + log y) / (log x * log y)) = 4 * (log a / (log x + log y)) := by 
      linarith [eq5a, h8']
    have eq5c : (log a * ((log x + log y) / (log x * log y))) * (log x * log y * (log x + log y)) = (4 * (log a / (log x + log y))) * (log x * log y * (log x + log y)) := by 
      rw [eq5b] 
    have h11 : (log a * ((log x + log y) / (log x * log y))) * (log x * log y * (log x + log y)) = log a * (log x + log y) * (log x + log y) := by 
      field_simp [h6, h7] 
      <;> ring 
    have h12 : (4 * (log a / (log x + log y))) * (log x * log y * (log x + log y)) = 4 * log a * (log x * log y) := by 
      field_simp [h7] 
      <;> ring 
    linarith [eq5c, h11, h12]
  have eq3 : (log x + log y) ^ 2 = 4 * (log x * log y) := by 
    have h5 : log a ≠ 0 := h5 
    have eq5' : log a * (log x + log y) * (log x + log y) = 4 * log a * (log x * log y) := eq5 
    apply (mul_left_inj' h5).mp 
    linarith 
  -- From `eq3` we show `log x = log y` by proving it's equivalent to `(log x - log y)^2 = 0`.
  have eq4 : (log x - log y) ^ 2 = 0 := by 
    nlinarith 
  have h13 : log x - log y = 0 := by 
    apply pow_eq_zero 
    exact eq4 
  have h14 : log x = log y := by 
    linarith 
  have h15 : x = y := by 
    have h14' : log x = log y := h14 
    have hx_pos' : x > 0 := hx1 
    have hy_pos' : y > 0 := hy1 
    exact log_injOn_pos (Set.mem_Ioi.mpr hx_pos') (Set.mem_Ioi.mpr hy_pos') h14'
  exact h15