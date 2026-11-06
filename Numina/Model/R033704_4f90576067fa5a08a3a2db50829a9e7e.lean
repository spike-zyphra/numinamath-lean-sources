import Mathlib

open Real

theorem algebra_8391 {a b : ℝ} (ha : 1 < b) (hb : b < a) (h : logb a b + logb b a = 5 / 2) :
    b / (a + 4) ≤ 1 / 4 := by
  have h1 : a > 1 := by linarith
  have h2 : logb a b = (log b) / (log a) := by
    field_simp [logb]
    all_goals linarith
  have h3 : logb b a = (log a) / (log b) := by
    field_simp [logb]
    all_goals linarith
  rw [h2, h3] at h

  have h4 : 0 < b := by linarith
  have h5 : 0 < a := by linarith
  have h6 : log b > 0 := by
    apply Real.log_pos
    linarith
  have h7 : log a > 0 := by
    apply Real.log_pos
    linarith

  have h8 : 2 * (log b) ^ 2 + 2 * (log a) ^ 2 = 5 * (log a * log b) := by
    field_simp at h
    nlinarith

  have h9 : (log a - 2 * log b) * (2 * log a - log b) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h9) with h10 h11
  · -- $\ln a = 2 \ln b$, so $a = b^2$
    have ha2 : log a = 2 * log b := by linarith
    have h12 : a = b ^ 2 := by
      have h13 : log a = (2 * log b) := by linarith
      have h14 : log a = log (b ^ 2) := by
        rw [h13]
        have h15 : log (b ^ 2) = 2 * log b := by
          simp [log_pow]
          <;> ring_nf <;> simp [log_pow]
        linarith [h15]
      have h16 : log (b ^ 2) = 2 * log b := by
        simp [log_pow]
      have h17 : a = b ^ 2 := by
        have h18 : log a = log (b ^ 2) := by
          linarith [h14]
        have h19 : a > 0 := by linarith
        have h20 : b ^ 2 > 0 := by nlinarith
        exact log_injOn_pos (Set.mem_Ioi.mpr h19) (Set.mem_Ioi.mpr h20) h18
      exact h17
    have h14 : b / (a + 4) = b / (b ^ 2 + 4) := by
      rw [h12]
      <;> ring_nf
    rw [h14]
    have h14 : b / (b ^ 2 + 4) ≤ 1 / 4 := by
      have h15 : 0 < (b : ℝ) := by linarith
      have h16 : b ^ 2 + 4 > 0 := by nlinarith
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (b - 2), mul_pos (show 0 < b by linarith) (show 0 < b by linarith)]
    linarith
  · -- Let's suppose $2 \ln a - \ln b = 0$, contradiction.
    have ha2 : log b = 2 * log a := by linarith
    have h12 : b = a ^ 2 := by
      have h13 : log b = 2 * log a := by linarith
      have h14 : log b = log (a ^ 2) := by
        rw [h13]
        have h15 : log (a ^ 2) = 2 * log a := by
          simp [log_pow]
          <;> ring_nf <;> simp [log_pow]
        linarith [h15]
      have h15 : log (a ^ 2) = 2 * log a := by
        simp [log_pow]
      have h16 : b > 0 := by linarith
      have h14' : a ^ 2 > 0 := by nlinarith
      have h17 : b = a ^ 2 := by
        have h18 : log b = log (a ^ 2) := by
          linarith [h14]
        have h19 : b > 0 := by linarith
        have h20 : a ^ 2 > 0 := by nlinarith
        exact log_injOn_pos (Set.mem_Ioi.mpr h19) (Set.mem_Ioi.mpr h20) h18
      exact h17
    nlinarith [show a > 0 by nlinarith, show b > 0 by nlinarith, sq_pos_of_pos (show 0 < a - 1 by linarith)]