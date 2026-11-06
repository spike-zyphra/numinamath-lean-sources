import Mathlib

theorem number_theory_159545 (a b c d : ℕ) (ha : 1 ≤ a ∧ a ≤ 9)
    (hb : 0 ≤ b ∧ b ≤ 9) (hc : 0 ≤ c ∧ c ≤ 9) (hd : 0 ≤ d ∧ d ≤ 9)
    (h : 6 * (1000 * a + 100 * b + 10 * c + d) =
      10000 * a + 1000 * a + 100 * c + 10 * b + d) :
    1982 = 1000 * a + 100 * b + 10 * c + d := by
  have h1 : 1 ≤ a := by 
    omega 
  have h2 : a ≤ 9 := by 
    omega 
  have h3 : 0 ≤ b := by 
    omega 
  have h4 : b ≤ 9 := by 
    omega 
  have h5 : 0 ≤ c := by 
    omega 
  have h6 : c ≤ 9 := by 
    omega 
  have h7 : 0 ≤ d := by 
    omega 
  have h8 : d ≤ 9 := by 
    omega 
  have eq1 : a = 1 := by
    omega 
  have eq2 : b = 9 := by
    omega 
  have eq3 : c = 8 := by
    omega 
  have eq4 : d = 2 := by
    omega 
  omega