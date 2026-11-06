import Mathlib

/-Do there exist three distinct positive real numbers a,b,c such that
the numbers a,b,c,b+c-a,c+a-b,a+b-c and a+b+c form a 7-term arithmetic
progression in some order? -/

theorem algebra_607801: ¬ ∃ a b c d: ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d
∧ ((a + b - c = a - d ∧ c + a - b = a + d ∧ b = a + 2 * d ∧ c = a + 3 * d
∧ b + c - a = a + 4 * d ∧ a + b + c = a + 5 * d) ∨ (a + b - c = a - d ∧ b = a + d ∧ c + a - b = a + 2 * d ∧ c = a + 3 * d
∧ b + c - a = a + 4 * d ∧ a + b + c = a + 5 * d)) := by
  by_contra! h
  obtain ⟨a, b, c, d, ha, hb, hc, hd, h⟩ := h
  rcases h with h | h
  -- case 1
  . have e1: c = a + b + c - 2 * d := by linarith
    have e2: b = a + b + c - 3 * d := by linarith
    have e3: a = a + b + c - 5 * d := by linarith
    have o: a + b + c = 5 * d := by nlinarith
    have i: a = 0 := by nlinarith
    simp [i] at ha
  -- case 2
  . have e1: c = a + b + c - 2 * d := by linarith
    have e2: b = a + b + c - 4 * d := by linarith
    have e3: a = a + b + c - 5 * d := by linarith
    have ad: a = 1 / 2 * d := by nlinarith
    have bd : b = 3 / 2 * d := by nlinarith
    have cd: c = 7 / 2 * d := by nlinarith
    have o: a + b - c = - 1 / 2 * d := by nlinarith
    have i: a + b - c = - (3 / 2) * d := by nlinarith
    have j: d = 0 := by nlinarith
    simp [j] at hd