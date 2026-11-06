import Mathlib
/- There is a five-digit number $ \overline { A B C D E } $, and Xiao Bei found that $ \overline { A B } \times \overline { C D E } $ equals one-sixth of the five-digit number. Find the value of $ \overline { A B C D E } $. -/
theorem number_theory_626808 (A B C D E : ℕ) (hA : 1 ≤ A ∧ A ≤ 9) (hB : 0 ≤ B ∧ B ≤ 9) (hC : 1 ≤ C ∧ C ≤ 9) (hD : 0 ≤ D ∧ D ≤ 9) (hE : 0 ≤ E ∧ E ≤ 9) (h : (A * 10 + B) * (C * 100 + D * 10 + E) * 6 = (A * 10000 + B * 1000 + C * 100 + D * 10 + E)) : A * 10000 + B * 1000 + C * 100 + D * 10 + E = 21168:= by
  -- Define a as the two-digit number AB
  set a:= A * 10 + B with ha
  -- Define b as the three-digit number CDE
  set b:= C * 100 + D * 10 + E with hb
  -- Clear the values to work with the variables directly
  clear_value a b
  -- Extract the bounds for each digit
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  rcases hD with ⟨hD1, hD2⟩
  rcases hE with ⟨hE1, hE2⟩
  -- Rewrite the five-digit number in terms of a and b
  rw [show A * 10000 + B * 1000 + C * 100 + D * 10 + E = 1000 * a + b by linarith] at h ⊢
  -- Prove that 6*a - 1 is positive
  have g1 : 6 * a - 1 > 0:= by omega
  -- Prove that 6*a - 1 divides 500
  have g2 : 6 * a - 1 ∣ 500:= by
    zify
    have g2 : 6 * a - 1 + 1 = 6 * a:= by omega
    zify at g2
    replace g2 : (↑(6 * a - 1) : ℤ) = 6 * a - 1:= by omega
    rw [g2]
    zify at h
    replace h : (6 * (↑a : ℤ) - 1) * (3 * b - 500) = 500:= by linarith
    rw [←h]
    simp
  -- Compute all divisors of 500
  have g3 : Nat.divisors 500 = {1, 2, 4, 5, 10, 20, 25, 50, 100, 125, 250, 500}:= by native_decide
  -- Show that 6*a - 1 is in the set of divisors of 500
  replace g2 : 6 * a - 1 ∈ Nat.divisors 500:= by refine Nat.mem_divisors.mpr ⟨g2, by omega⟩
  rw [g3] at g2
  simp at g2
  -- Case analysis on all possible values of 6*a - 1
  rcases g2 with g2 | g2 | g2 | g2 | g2 | g2 | g2 | g2 | g2 | g2 | g2 | g2
  -- Most cases lead to contradictions with the digit bounds
  any_goals
    omega
  .
    -- The only valid case: 6*a - 1 = 125, so a = 21
    replace g2 : a = 21:= by omega
    rw [g2] at h ⊢
    -- From the equation, we get b = 168
    replace h : b = 168:= by omega
    rw [h]
