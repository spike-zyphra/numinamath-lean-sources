import Mathlib

open Real

theorem algebra_278293 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (P : ℝ) (hP : 0 < P) :
    logb (a^2) P = logb a P / 2 ∧ logb (sqrt a) P = 2 * logb a P ∧
    logb (1 / a) P = -logb a P := by
  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2

  constructor
  · -- We need to prove that $\log_{a^2} P = \frac{\log_a P}{2}$
    have h1 : logb (a^2) P = logb a P / 2 := by
      have h2 : logb (a ^ 2) P = (log P) / (log (a ^ 2)) := by
        field_simp [logb]
      have h3 : log (a ^ 2) = 2 * log a := by
        simp [log_pow]
      have h4 : logb a P = (log P) / (log a) := by
        field_simp [logb]
      rw [h2, h3, h4]
      <;> field_simp <;> ring
    exact h1
  constructor
  · -- We need to prove that $\log_{\sqrt{a}} P = 2 \log_a P$
    have h2 : logb (sqrt a) P = 2 * logb a P := by
      have h5 : logb (sqrt a) P = (log P) / (log (sqrt a)) := by
        field_simp [logb]
      have h6 : log (sqrt a) = (1 / 2) * log a := by
        have h7 : sqrt a = a ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [h7]
        have h8 : log (a ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * log a := by
          rw [log_rpow]
          all_goals linarith
        linarith
      have h7 : logb a P = (log P) / (log a) := by
        field_simp [logb]
      rw [h5, h6, h7]
      <;> field_simp <;> ring_nf
    exact h2
  · -- We need to prove that $\log_{\frac{1}{a}} P = -\log_a P$
    have h3 : logb (1 / a) P = -logb a P := by
      have h8 : logb (1 / a) P = (log P) / (log (1 / a)) := by
        field_simp [logb]
      have h9 : log (1 / a) = -log a := by
        simp [log_div, log_one]
      have h10 : logb a P = (log P) / (log a) := by
        field_simp [logb]
      rw [h8, h9, h10]
      <;> field_simp <;> ring_nf
    exact h3