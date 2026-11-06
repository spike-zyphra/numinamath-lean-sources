import Mathlib

theorem algebra_274340 (a : ℕ → ℤ) (ha : Monotone a)
    (hpos : ∀ n, 0 < a n) (hf : ∀ n, a (n + 2) = 3 * a (n + 1) - a n)
    (h6 : a 6 = 280) : a 7 = 733 := by
  have h1 : a 0 ≤ a 1 := by
    apply ha
    all_goals
    simp
  have h2 : a 1 ≤ a 2 := by
    apply ha
    all_goals
    simp
  have h3 : a 2 ≤ a 3 := by
    apply ha
    all_goals
    simp
  have h4 : a 3 ≤ a 4 := by
    apply ha
    all_goals
    simp
  have h5 : a 4 ≤ a 5 := by
    apply ha
    all_goals
    simp
  have h6' : a 5 ≤ a 6 := by
    apply ha
    all_goals
    simp
  have eq1 : a 2 = 3 * a 1 - a 0 := by
    specialize hf 0
    simpa using hf
  have eq2 : a 3 = 3 * a 2 - a 1 := by
    specialize hf 1
    simpa using hf
  have eq3 : a 4 = 3 * a 3 - a 2 := by
    specialize hf 2
    simpa using hf
  have eq4 : a 5 = 3 * a 4 - a 3 := by
    specialize hf 3
    simpa using hf
  have eq5 : a 6 = 3 * a 5 - a 4 := by
    specialize hf 4
    simpa using hf
  have eq6 : a 7 = 3 * a 6 - a 5 := by
    specialize hf 5
    simpa using hf
  have h7 : 0 < a 0 := hpos 0
  have h8 : 0 < a 1 := hpos 1
  have h9 : 0 < a 2 := hpos 2
  have h10 : 0 < a 3 := hpos 3
  have h11 : 0 < a 4 := hpos 4
  have h12 : 0 < a 5 := hpos 5
  have h13 : 0 < a 6 := hpos 6
  omega