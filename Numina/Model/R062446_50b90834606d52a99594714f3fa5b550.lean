import Mathlib

theorem algebra_239106 {a b c : ℕ} (ha : a^2 + a * b + a * c = 20) (hb : a * b + b^2 + b * c = 30)
    (hc : a * c + b * c + c^2 = 50) :
    a = 2 ∧ b = 3 ∧ c = 5 := by
  have h1 : (a + b + c) ^ 2 = 100 := by
    nlinarith [ha, hb, hc]
  have h2 : a + b + c = 10 := by
    nlinarith
  have ha2 : a = 2 := by
      -- From equation (1) and the sum, we derive a = 2.
      have h4 : b + c = 10 - a := by
        omega
      nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), sq_nonneg (c : ℕ), h2]
  have h10 : b + c = 8 := by
    omega
  have hb2 : b = 3 := by
    rw [show a = 2 by omega] at hb
    have hc1 : c = 8 - b := by
      omega
    rw [show c = 8 - b by omega] at hb
    nlinarith [hb]
  have hc2 : c = 5 := by
    omega
  simp [ha2, hb2, hc2]
  <;> tauto