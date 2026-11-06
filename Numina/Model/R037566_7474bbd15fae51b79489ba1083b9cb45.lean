import Mathlib

theorem number_theory_52393 (n : ℕ) (hn : n > 0) :
    ∃ x y, Odd x ∧ Odd y ∧ (2^n : ℤ) = 5 * x * y - x ^ 2 - 2 * y ^ 2 := by

  have h1 : ∀ n : ℕ, n > 0 → ∃ x y, Odd x ∧ Odd y ∧ (2^n : ℤ) = 5 * x * y - x ^ 2 - 2 * y ^ 2 := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        use 1, 1
        constructor
        · decide
        constructor
        · decide
        · norm_num
      | succ n =>
        rcases ih (by linarith) with ⟨x, y, hx, hy, heq⟩
        use 5 * x - 2 * y, x
        constructor
        · -- Show that 5 * x - 2 * y is odd
          have hx' : Odd (5 * x - 2 * y) := by
            have hx1 : (x : ℤ) % 2 = 1 := by
              obtain ⟨k, hk⟩ := hx
              omega
            have hy1 : (y : ℤ) % 2 = 1 := by
              obtain ⟨k, hk⟩ := hy
              omega
            have hx1 : (5 * (x : ℤ) - 2 * (y : ℤ)) % 2 = 1 := by
              omega
            have : ∃ k, (5 * x - 2 * y : ℤ) = 2 * k + 1 := by
              have : (5 * x - 2 * y : ℤ) % 2 = 1 := hx1
              refine' ⟨(5 * x - 2 * y - 1) / 2, by omega⟩
            rcases this with ⟨k, hk⟩
            exact ⟨k, by linarith⟩
          exact hx'
        constructor
        · -- Show that x is odd 
          exact hx
        · -- Show the equation holds 
          have eq1 : (2 : ℤ) ^ (n + 1 + 1) = 2 * (2 ^ (n + 1)) := by
            ring_nf
          have eq2 : (2 : ℤ) ^ (n + 1) = 5 * x * y - x ^ 2 - 2 * y ^ 2 := by
            linarith [heq]
          nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (5 * x - 2 * y), sq_nonneg (x - y)]
  specialize h1 n hn
  simpa using h1