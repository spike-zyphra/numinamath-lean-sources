import Mathlib

theorem number_theory_195741 (a b S d : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9)
    (hS : 0 ≤ S ∧ S ≤ 9) (hd : 0 ≤ d ∧ d ≤ 9)
    (h : (1000 * a + 100 * b + 10 * S + d) * 9 = 1000 * d + 100 * S + 10 * b + a) :
    S = 8 := by
  -- Derivations of bounds from hypotheses.
  have h1 : a ≤ 9 := ha.right
  have h2 : 1 ≤ a := ha.left
  have h3 : b ≤ 9 := hb.right
  have h4 : 0 ≤ b := hb.left
  have h5 : S ≤ 9 := hS.right
  have h6 : 0 ≤ S := hS.left
  have h7 : d ≤ 9 := hd.right
  have h8 : 0 ≤ d := hd.left

  interval_cases a <;> interval_cases b <;> omega