import Mathlib

theorem algebra_136663 (a b c d : ℕ) :
    a^2 - c^2 = 1024 ∧ b^2 - d^2 = 1024 ∧ a * b + b * c + c * d + d * a = 1024 ↔
    (a = 32 ∧ b = 32 ∧ c = 0 ∧ d = 0) := by
  constructor
  · -- Assume the equations hold, prove (a,b,c,d) = (32,32,0,0)
    rintro ⟨h1, h2, h3⟩
    have eq1 : a^2 = c^2 + 1024 := by
      omega
    have eq2 : b^2 = d^2 + 1024 := by
      omega
    have eq3 : (a + c) * (b + d) = 1024 := by
      nlinarith
    have h4 : a + c ≤ 32 := by
      nlinarith [sq_nonneg (a + c - 32 : ℤ), sq_nonneg (b + d - 32 : ℤ), sq_nonneg (a - 32 : ℤ), sq_nonneg (b - 32 : ℤ), sq_nonneg (c : ℤ), sq_nonneg (d : ℤ)]
    have h5 : b + d ≤ 32 := by
      nlinarith [sq_nonneg (a + c - 32 : ℤ), sq_nonneg (b + d - 32 : ℤ), sq_nonneg (a - 32 : ℤ), sq_nonneg (b - 32 : ℤ), sq_nonneg (c : ℤ), sq_nonneg (d : ℤ)]
    have h6 : a ≤ 32 := by
      nlinarith [show a + c ≤ 32 by linarith]
    have h7 : c ≤ 32 := by
      nlinarith [show a + c ≤ 32 by linarith, h6]
    have h8 : b ≤ 32 := by
      nlinarith [show b + d ≤ 32 by linarith]
    have h9 : d ≤ 32 := by
      nlinarith [show b + d ≤ 32 by linarith, h8]
    interval_cases a <;> interval_cases b <;> omega
  · -- Assume (a,b,c,d) = (32,32,0,0), prove the equations
    rintro ⟨ha, hb, hc, hd⟩
    rw [ha, hb, hc, hd]
    all_goals
      omega