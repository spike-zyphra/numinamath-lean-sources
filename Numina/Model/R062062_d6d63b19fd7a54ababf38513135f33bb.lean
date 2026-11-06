import Mathlib

open Real

theorem inequalities_7288 : IsGreatest {c | ∀ x y : ℝ, x > 0 → y > 0 → (x + y) / x + (x + y) / y ≥ c} 4 := by
  constructor 
  · -- First, we show that 4 is in the set
    intro x y hx hy
    have h1 : (x + y) / x + (x + y) / y ≥ 4 := by
      have h2 : (x + y) / x + (x + y) / y - 4 ≥ 0 := by
        have h3 : (x + y) / x + (x + y) / y - 4 = ((x + y) * y + (x + y) * x - 4 * x * y) / (x * y) := by 
          field_simp [hx.ne.symm, hy.ne.symm]
          <;> ring
        rw [h3]
        have h4 : ((x + y) * y + (x + y) * x - 4 * x * y) = (x - y) ^ 2 := by
          linarith [sq_nonneg (x - y)]
        rw [h4]
        have h5 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
        have h6 : x * y > 0 := mul_pos hx hy
        apply div_nonneg
        · exact h5
        · linarith
      linarith
    linarith [h1]
  · -- Second, we show that 4 is greatest in the set
    intro c hc
    have h1 : ∀ x y : ℝ, x > 0 → y > 0 → (x + y) / x + (x + y) / y ≥ c := hc
    have h2 := h1 1 1 (by norm_num) (by norm_num)
    norm_num at h2
    linarith