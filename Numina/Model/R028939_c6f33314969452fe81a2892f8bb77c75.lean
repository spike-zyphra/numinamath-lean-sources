import Mathlib

open Real

theorem calculus_229012 {a x : ℝ} (ha : 0 < a ∧ a ≠ 1) (hx : 0 < x) :
    deriv (logb a) x = 1 / (x * log a) := by
  have hlog : log a ≠ 0 := by
    have ha1 : 0 < a := ha.1
    have ha2 : a ≠ 1 := ha.2
    exact log_ne_zero_of_pos_of_ne_one ha1 ha2
  have h2 : deriv (logb a) x = deriv (fun (y : ℝ) => (log y) / log a) x := by
    have h_eq : (logb a) = (fun (y : ℝ) => (log y) / log a) := by
      funext y
      have hy : logb a y = (log y) / log a := by
        field_simp [logb]
      simpa using hy
    rw [h_eq]
  rw [h2]
  simp [deriv_div_const, deriv_log, mul_comm]
  <;> field_simp [show log a ≠ 0 by assumption, hx.ne.symm]
  <;> ring_nf