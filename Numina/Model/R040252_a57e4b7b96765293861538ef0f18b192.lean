import Mathlib

theorem algebra_237164 {p : Polynomial ℤ} (n : ℤ) (h₁ : p.eval (-n) < p.eval n) (h₂ : p.eval n < n) :
    p.eval (-n) < -n := by
  have h : p.eval n - p.eval (-n) > 0 := by linarith
  obtain ⟨k, h3⟩ := Polynomial.sub_dvd_eval_sub n (-n) p
  have hk_eq : p.eval n - p.eval (-n) = k * (n - (-n)) := by
    have h7 : p.eval n - p.eval (-n) = (n - (-n)) * k := by
      simpa [show n - (-n) = n - (-n) by ring] using h3
    calc
      p.eval n - p.eval (-n) = (n - (-n)) * k := h7
      _ = k * (n - (-n)) := by ring
  by_contra h'
  push_neg at h'
  have h_pos : p.eval n - p.eval (-n) < 2 * n := by
    have h₃ : p.eval n < n := h₂
    have h₄ : p.eval (-n) ≥ -n := by linarith
    nlinarith
  have hk_eq' : p.eval n - p.eval (-n) = k * (2 * n) := by
    rw [show n - (-n) = 2 * n by ring] at hk_eq
    linarith
  by_cases hn : n > 0
  · -- If n > 0
    have h_pos_k : k > 0 := by
      nlinarith
    have h_neg_k : k < 1 := by
      nlinarith
    omega
  · -- If n ≤ 0
    have h_le : n ≤ 0 := by linarith
    by_cases hn_zero : n = 0
    · -- If n = 0 
      rw [hn_zero] at h₁ h₂
      all_goals 
        linarith
    · -- If n ≠ 0
      have h_neg : n < 0 := by
        by_contra h'
        push_neg at h'
        have : n = 0 := by linarith
        contradiction
      have h_pos_neg : -n > 0 := by linarith
      nlinarith