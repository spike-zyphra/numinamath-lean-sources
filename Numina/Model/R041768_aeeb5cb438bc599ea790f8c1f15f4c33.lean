import Mathlib

theorem number_theory_226154 (a b : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n ∧ 0 < b n)
    (h10 : a 10 = b 10 ∧ b 10 < 2017) (hadd : ∀ n, a (n + 2) = a (n + 1) + a n)
    (hmul : ∀ n, b (n + 1) = 2 * b n) :
    a 1 + b 1 = 13 ∨ a 1 + b 1 = 20 := by
  have h2 : b 0 > 0 := by
    specialize hpos 0
    omega
  have hb1_pos : b 1 > 0 := by
    specialize hpos 1
    omega
  have ha0_pos : a 0 > 0 := by
    specialize hpos 0
    omega
  have ha1_pos : a 1 > 0 := by
    specialize hpos 1
    omega
  have eq1 : b 10 = 1024 * b 0 := by
    simp [hmul] <;> omega
  have eq2 : b 10 < 2017 := by
    omega
  have eq3 : a 10 = b 10 := by
    omega
  have hb0_eq1 : b 0 = 1 := by
    omega
  have hb1_eq : b 1 = 2 := by
    specialize hmul 0
    simp [hb0_eq1] at hmul
    omega
  have h3 : a 10 = 1024 := by
    omega
  have eq4 : a 2 = a 1 + a 0 := by
    specialize hadd 0
    simpa using hadd
  have eq5 : a 3 = a 2 + a 1 := by
    specialize hadd 1
    simpa using hadd
  have eq6 : a 4 = a 3 + a 2 := by
    specialize hadd 2
    simpa using hadd
  have eq7 : a 5 = a 4 + a 3 := by
    specialize hadd 3
    simpa using hadd
  have eq8 : a 6 = a 5 + a 4 := by
    specialize hadd 4
    simpa using hadd
  have eq9 : a 7 = a 6 + a 5 := by
    specialize hadd 5
    simpa using hadd
  have eq10 : a 8 = a 7 + a 6 := by
    specialize hadd 6
    simpa using hadd
  have eq11 : a 9 = a 8 + a 7 := by
    specialize hadd 7
    simpa using hadd
  have eq12 : a 10 = a 9 + a 8 := by
    specialize hadd 8
    simpa using hadd
  -- The Lean 4 omega solver can solve linear arithmetic with constraints. In Lean 4, omega works for algebra which would be minimally reduced.
  omega