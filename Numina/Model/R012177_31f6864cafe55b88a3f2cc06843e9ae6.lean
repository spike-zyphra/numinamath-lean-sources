import Mathlib

theorem number_theorem_210996
  (A B a b c : ℕ)
  (ha : 0 < a ∧ a ≤ 9)
  (hb : 0 < b ∧ b ≤ 9)
  (hc : c ≤ 9)
  (hA : A = 10 * a + c)
  (hB : B = 10 * b + c)
  (hAB : A > B)
  (hAB1 : A / 9 = B % 9)
  (hAB2 : B / 9 = A % 9) :
  A = 75 ∧ B = 35 ∨ A = 65 ∧ B = 25 ∨ A = 55 ∧ B = 15 := by
  rw [hA] at hAB1 hAB2 hAB
  rw [hB] at hAB1 hAB2
  have h1 : a ≤ 9 := ha.right
  have h2 : b ≤ 9 := hb.right
  have ha1 : 0 < a := ha.1
  have hb1 : 0 < b := hb.1
  have h3 : c ≤ 9 := hc
  interval_cases a <;> interval_cases b 
    <;> try { 
      omega 
    }