import Mathlib

open Real

lemma Real.mul_le_mul_of_nonneg_left' {a b c : ℝ} (h : a ≤ b) (hc : c ≥ 0) :
    c * a ≤ c * b := by
  have : c * a ≤ c * b := by
    apply mul_le_mul_of_nonneg_left
    exact h
    positivity
  assumption

lemma lemma_1 (x : ℝ) (hx : x > 0) : log x ≤ x - 1 := by
  have h1 : log x ≤ x - 1 := by
    linarith [Real.log_le_sub_one_of_pos hx]
  exact h1

theorem inequalities_220851 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ b * b ^ c * c ^ a ≤ a ^ a * b ^ b * c ^ c := by
  have h1 : a ^ b * b ^ c * c ^ a ≤ a ^ a * b ^ b * c ^ c := by
    have h2 : b * (Real.log a) + c * (Real.log b) + a * (Real.log c) ≤ a * (Real.log a) + b * (Real.log b) + c * (Real.log c) := by
      have h3 : (a - b) * (Real.log a - Real.log b) ≥ 0 := by
        by_cases h' : a ≥ b
        · -- Since $a \geq b$ and $\ln a \geq \ln b$, $(a-b)(\ln a - \ln b) \geq 0$.
          have h1 : a ≥ b := by linarith
          have h2 : Real.log a ≥ Real.log b := by
            apply Real.log_le_log
            all_goals
              linarith
          nlinarith
        · -- Since $a < b$ and $\ln a < \ln b$, $(a-b)(\ln a - \ln b) \geq 0$.
          have h1 : b ≥ a := by linarith
          have h2 : Real.log b ≥ Real.log a := by
            apply Real.log_le_log
            all_goals
              linarith
          nlinarith
      have h4 : (b - c) * (Real.log b - Real.log c) ≥ 0 := by
        by_cases h' : b ≥ c
        · -- Since $b \geq c$ and $\ln b \geq \ln c$, $(b-c)(\ln b - \ln c) \geq 0$.
          have h1 : b ≥ c := by linarith
          have h2 : Real.log b ≥ Real.log c := by
            apply Real.log_le_log
            all_goals
              linarith
          nlinarith
        · -- Since $b < c$ and $\ln b < \ln c$, $(b-c)(\ln b - \ln c) \geq 0$.
          have h1 : c ≥ b := by linarith
          have h2 : Real.log c ≥ Real.log b := by
            apply Real.log_le_log
            all_goals
              linarith
          nlinarith
      have h5 : (c - a) * (Real.log c - Real.log a) ≥ 0 := by
        by_cases h' : c ≥ a
        · -- Since $c \geq a$ and $\ln c \geq \ln a$, $(c-a)(\ln c - \ln a) \geq 0$.
          have h1 : c ≥ a := by linarith
          have h2 : Real.log c ≥ Real.log a := by
            apply Real.log_le_log
            all_goals
              linarith
          nlinarith
        · -- Since $c < a$ and $\ln c < \ln a$, $(c-a)(\ln c - \ln a) \geq 0$.
          have h1 : a ≥ c := by linarith
          have h2 : Real.log a ≥ Real.log c := by
            apply Real.log_le_log
            all_goals
              linarith
          nlinarith
      nlinarith
    have h3 : Real.log (a ^ b * b ^ c * c ^ a) = b * (Real.log a) + c * (Real.log b) + a * (Real.log c) := by
      have h4 : Real.log (a ^ b * b ^ c * c ^ a) = Real.log (a ^ b) + Real.log (b ^ c) + Real.log (c ^ a) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      have h5 : Real.log (a ^ b) = b * Real.log a := by
        rw [Real.log_rpow]
        all_goals
          positivity
      have h6 : Real.log (b ^ c) = c * Real.log b := by
        rw [Real.log_rpow]
        all_goals
          positivity
      have h7 : Real.log (c ^ a) = a * Real.log c := by
        rw [Real.log_rpow]
        all_goals
          positivity
      rw [h4, h5, h6, h7]
    have h4 : Real.log (a ^ a * b ^ b * c ^ c) = a * (Real.log a) + b * (Real.log b) + c * (Real.log c) := by
      have h5 : Real.log (a ^ a * b ^ b * c ^ c) = Real.log (a ^ a) + Real.log (b ^ b) + Real.log (c ^ c) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      have h6 : Real.log (a ^ a) = a * Real.log a := by
        rw [Real.log_rpow]
        all_goals
          positivity
      have h7 : Real.log (b ^ b) = b * Real.log b := by
        rw [Real.log_rpow]
        all_goals
          positivity
      have h8 : Real.log (c ^ c) = c * Real.log c := by
        rw [Real.log_rpow]
        all_goals
          positivity
      rw [h5, h6, h7, h8]
    have h5 : Real.log (a ^ b * b ^ c * c ^ a) ≤ Real.log (a ^ a * b ^ b * c ^ c) := by
      nlinarith [h3, h4, h2]
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h5
  assumption