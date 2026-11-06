import Mathlib

theorem number_theory_4385 (a b : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9)
    (h : Nat.ofDigits 10 [b, 0, a] = 9 * Nat.ofDigits 10 [b, a]) :
    Nat.ofDigits 10 [b, a] = 45 := by
  simp [Nat.ofDigits, List.foldl] at h ⊢
  have h1 : a ≤ 9 := ha.right
  have h2 : 1 ≤ a := ha.left
  have h3 : 0 ≤ b := hb.left
  have h4 : b ≤ 9 := hb.right
  interval_cases a <;> interval_cases b <;> omega