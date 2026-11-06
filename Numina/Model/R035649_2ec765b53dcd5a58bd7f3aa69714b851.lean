import Mathlib

theorem number_theory_119857 (a b c : ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10)
    (h : 2216 / (5 * 10 + a) = 4 * 10 + b) (h' : 2216 % (5 * 10 + a) = 2 * 10 + c)
    (h'' : Nat.Prime (2 * 10 + c)) :
    a = 1 ∧ b = 3 ∧ c = 3 := by
  have h1 : a < 10 := by linarith
  have h2 : b < 10 := by linarith
  have h3 : c < 10 := by linarith
  interval_cases a <;> interval_cases b <;> interval_cases c 
    <;> norm_num at h h' h'' ⊢ 
    <;> tauto