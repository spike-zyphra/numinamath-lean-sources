import Mathlib

open Real Set

theorem algebra_100084 :
    IsLeast {z : ℝ | ∃ x y, x > 1 ∧ y > 1 ∧ z = (logb x 2011 + logb y 2011) / logb (x * y) 2011} 4 := by
  constructor
  · -- Show 4 is in the set.
    use 2011, 2011
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show that with x = y = 2011, the value is 4.
      have h1 : logb (2011 : ℝ) 2011 = 1 := by 
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h2 : logb (2011 * 2011 : ℝ) 2011 = 1 / 2 := by
        have h3 : logb (2011 * 2011) 2011 = (log 2011) / (log (2011 * 2011)) := by 
          field_simp [logb]
        have h4 : log (2011 * 2011) = 2 * log 2011 := by 
          calc 
            log (2011 * 2011) = log 2011 + log 2011 := by rw [log_mul (by norm_num) (by norm_num)]
            _ = 2 * log 2011 := by ring
        rw [h3, h4]
        have h5 : log 2011 > 0 := by 
          apply log_pos
          norm_num
        field_simp [h5]
        <;> ring_nf
      rw [h1, h2]
      norm_num
  · -- Show that 4 is the least element in the set.
    intro z hz
    rcases hz with ⟨x, y, hx, hy, hz⟩
    have hx1 : log x > 0 := by
      apply log_pos
      linarith
    have hy1 : log y > 0 := by
      apply log_pos
      linarith
    have h1 : logb x 2011 = log 2011 / log x := by 
      field_simp [logb]
    have h2 : logb y 2011 = log 2011 / log y := by 
      field_simp [logb]
    have h3 : logb (x * y) 2011 = log 2011 / log (x * y) := by 
      field_simp [logb]
    have h4 : log (x * y) = log x + log y := by 
      rw [log_mul (by linarith) (by linarith)]
    rw [h1, h2, h3, h4] at hz
    have hx2 : log 2011 > 0 := by
      apply log_pos
      norm_num
    have h6 : (log 2011 / log x + log 2011 / log y) / (log 2011 / (log x + log y)) = (log x + log y) * (1 / log x + 1 / log y) := by
      field_simp [show log x > 0 by linarith, show log y > 0 by linarith, show log 2011 > 0 by linarith]
      <;> ring_nf <;> field_simp
    have h7 : (log x + log y) * (1 / log x + 1 / log y) ≥ 4 := by 
      have h8 : (log x + log y) * (1 / log x + 1 / log y) = 2 + (log x / log y) + (log y / log x) := by 
        field_simp [show log x > 0 by linarith, show log y > 0 by linarith]
        ring
      rw [h8]
      have h9 : (log x / log y) + (log y / log x) ≥ 2 := by
        have hx2 : log x > 0 := by
          apply log_pos
          linarith
        have hy2 : log y > 0 := by
          apply log_pos
          linarith
        have h4 : (log x / log y + (log y / log x) - (2 : ℝ)) ≥ 0 := by
          have hx4 : (log x / log y + (log y / log x) - (2 : ℝ)) = (log x - log y) ^ 2 / (log x * log y) := by
            field_simp [show log x > 0 by linarith, show log y > 0 by linarith]
            ring
          rw [hx4]
          have hx5 : (log x - log y) ^ 2 ≥ 0 := by 
            exact sq_nonneg (log x - log y)
          have hx6 : log x * log y > 0 := by
            positivity
          exact div_nonneg hx5 (by positivity)
        linarith 
      linarith 
    rw [hz]
    rw [h6]
    linarith [h7]