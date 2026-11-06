import Mathlib

theorem number_theory_183266 :
    IsGreatest {n | ∃ a b : ℕ, 0 < a ∧ a ≤ 100 ∧ 0 < b ∧ b ≤ 100 ∧ a * b = (Nat.lcm a b / Nat.gcd a b) ^ 2 ∧ n = a + b} 78 := by
  constructor
  · -- First we show 78 is achievable with a = 54 and b = 24
    use 54, 24
    repeat { constructor }
    all_goals norm_num
  · -- Now we prove that 78 is the greatest
    intro n hn
    rcases hn with ⟨a, b, ha_pos, ha_le, hb_pos, hb_le, heq, hsum⟩
    by_contra h
    push_neg at h
    have h1 : a + b > 78 := by linarith [hsum, h]
    have h2 : a ≤ 100 := by linarith
    have h3 : b ≤ 100 := by linarith
    have h4 : a > 0 := by linarith
    have h5 : b > 0 := by linarith
    interval_cases a <;> interval_cases b
    <;> norm_num at heq ⊢
    <;> omega