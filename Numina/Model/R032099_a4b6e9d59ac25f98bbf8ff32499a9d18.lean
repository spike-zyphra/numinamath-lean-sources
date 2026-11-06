import Mathlib

theorem algebra_21328 : IsGreatest {x | ∃(a b: ℕ), a > 0 ∧ b > 0 ∧ (a * b) + (a + b) = 454 ∧ x = (a + b) * (a * b)} 33840 := by 
  constructor
  · -- Show that 33840 is in the set.
    use 4, 90
    all_goals norm_num
  · -- Show that 33840 is greatest.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, heq, hx⟩
    have h1 : a * b + (a + b) = 454 := heq
    have h2 : a ≤ 227 := by
      nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), h1, mul_pos ha hb]
    have h3 : b ≤ 227 := by
      nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), h1, mul_pos ha hb]
    interval_cases a <;> norm_num at heq hx ⊢
    <;> try { 
      omega
    }
    <;> try { 
      nlinarith [sq_nonneg (b : ℕ), sq_nonneg (b - 4 : ℤ), sq_nonneg (b - 6 : ℤ), sq_nonneg (b - 12 : ℤ), sq_nonneg (b - 34 : ℤ), sq_nonneg (b - 64 : ℤ), sq_nonneg (b - 90 : ℤ)]
    }