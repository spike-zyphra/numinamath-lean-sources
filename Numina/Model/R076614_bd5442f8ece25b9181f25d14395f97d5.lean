import Mathlib

theorem algebra_117516 {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (h : Real.log (a + b) = Real.log a + Real.log b) :
    Real.log (a - 1) + Real.log (b - 1) = 0 := by
  have h1 : a + b > 0 := by nlinarith
  have ha2 : a > 0 := by linarith
  have hb2 : b > 0 := by linarith
  have h2 : Real.log (a + b) = Real.log (a * b) := by
    have h_mul : Real.log (a * b) = Real.log a + Real.log b := by
      rw [Real.log_mul (by linarith) (by linarith)]
    linarith [h, h_mul]
  have h3 : a + b = a * b := by
    have h_inj : Real.log (a + b) = Real.log (a * b) := h2
    have h4 : a + b > 0 := by nlinarith
    have h5 : a * b > 0 := mul_pos ha2 hb2
    have h6 : (a + b) = (a * b) := by
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr h4) (Set.mem_Ioi.mpr h5) h_inj
    exact h6
  have h4 : (a - 1) * (b - 1) = 1 := by
    nlinarith
  have ha3 : a - 1 > 0 := by linarith
  have hb3 : b - 1 > 0 := by linarith
  have h5 : Real.log (a - 1) + Real.log (b - 1) = Real.log ((a - 1) * (b - 1)) := by
    rw [Real.log_mul (by linarith) (by linarith)]
  rw [h5]
  rw [h4]
  simp