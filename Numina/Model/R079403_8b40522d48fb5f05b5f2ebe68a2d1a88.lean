import Mathlib

theorem number_theory_11179 (a : ℕ → ℕ) (ha1 : 0 < a 1)
    (han : ∀ n, a (n + 1) = a n + Nat.gcd (n + 1) (a n)) (ha2 : a 1 = a 0) :
    (a 0 > 3 → {k | 0 < a k ∧ a k = 2 * k}.Finite ∧
      Set.encard {k | 0 < a k ∧ a k = 2 * k} = a 0 - 3) ∧
    (a 0 ≤ 3 → {k | 0 < a k ∧ a k = 2 * k} = ∅) := by
  have ha3 : a 1 = a 0 + 1 := by 
    have h_coeff : a 1 = a 0 + Nat.gcd 1 (a 0) := by
      specialize han 0
      norm_num at han ⊢ 
      exact han 
    calc 
      a 1 = a 0 + Nat.gcd 1 (a 0) := by exact h_coeff 
      _ = a 0 + 1 := by 
        simp [Nat.gcd_one_left]
  -- Now we have both a 1 = a 0 and a 1 = a 0 + 1
  -- These are contradictory 
  have h1 : a 1 = a 0 := ha2 
  -- Since a 1 = a 0 and a 1 = a 0 + 1
  -- We have a 0 = a 0 + 1
  linarith [ha3, h1, ha1]