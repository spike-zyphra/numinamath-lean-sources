import Mathlib

theorem algebra_253762 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : b = a^2 - a) (h2 : c = b^2 - b) (h3 : a = c^2 - c) :
    a = 2 ∧ b = 2 ∧ c = 2 := by
  have eq1 : a ^ 2 = a + b := by
    have h4 : a ≤ a ^ 2 := by
      have h : a ≥ 1 := by linarith
      nlinarith [sq_nonneg (a : ℕ)]
    omega
  have eq2 : b ^ 2 = b + c := by
    have h4 : b ≤ b ^ 2 := by
      have h : b ≥ 1 := by linarith
      nlinarith [sq_nonneg (b : ℕ)]
    omega
  have eq3 : c ^ 2 = c + a := by
    have h4 : c ≤ c ^ 2 := by
      have h : c ≥ 1 := by linarith
      nlinarith [sq_nonneg (c : ℕ)]
    omega
  have h4 : a ≤ 2 := by
    by_contra h
    push_neg at h
    have h4 : a ≥ 3 := by omega
    have h4a : b ≥ 6 := by
      nlinarith [sq_nonneg (a : ℕ), h4]
    have h5 : c ≥ 30 := by
      nlinarith [sq_nonneg (b : ℕ), h4a]
    have h6 : a ≥ 870 := by
      nlinarith [sq_nonneg (c : ℕ), h5]
    nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), sq_nonneg (c : ℕ)]
  have h5 : a = 1 ∨ a = 2 := by
    interval_cases a <;> tauto
  rcases h5 with (ha1 | ha2)
  · -- a = 1
    have ha1' : a = 1 := by
      omega
    have hb0 : b = 0 := by
      rw [show a = 1 by omega] at h1
      omega
    omega
  · -- a = 2
    have ha2' : a = 2 := by
      omega
    have hb2 : b = 2 := by
      rw [show a = 2 by omega] at h1
      omega
    have hc2 : c = 2 := by
      rw [show b = 2 by omega] at h2
      omega
    exact ⟨by omega, by omega, by omega⟩