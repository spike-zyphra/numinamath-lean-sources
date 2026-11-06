import Mathlib

theorem algebra_21323 (total_households : ℕ) (h : total_households ≠ 0)
    (h1 : (40 / 100 : ℝ) * total_households + (30 / 100 : ℝ) * total_households +
      (20 / 100 : ℝ) * total_households + (10 / 100 : ℝ) * total_households = total_households) :
    (90 / 100 : ℝ) * total_households = total_households - (10 / 100 : ℝ) * total_households := by
  -- This is just an algebraic equality which Lean can prove directly
  ring_nf
  <;> linarith