import Mathlib

open Real

theorem algebra_11612 {a : ℕ → ℝ}
    (ha1 : a 1 > 0)
    (han : ∀ n, a (n + 1) = sqrt ((3 + a n) / 2))
    : (∀ n, 0 < n → a (n + 1) > a n) ↔ 0 < a 1 ∧ a 1 < 3 / 2 := by
  constructor
  · -- Assume that for all positive n, a (n + 1) > a n, prove 0 < a 1 ∧ a 1 < 3 / 2
    intro h
    have ha21 : a 2 > a 1 := h 1 (by norm_num)
    have ha2_eq : a 2 = sqrt ((3 + a 1) / 2) := by
      specialize han 1
      norm_num at han ⊢
      linarith
    have h2 : a 1 < 3 / 2 := by
      have h3 : sqrt ((3 + a 1) / 2) > a 1 := by linarith [ha2_eq, ha21]
      have h3a : 0 ≤ (3 + a 1) / 2 := by
        nlinarith [ha1]
      have h7 : (sqrt ((3 + a 1) / 2)) ^ 2 = (3 + a 1) / 2 := by
        rw [Real.sq_sqrt]
        nlinarith [ha1]
      have h6 : (sqrt ((3 + a 1) / 2)) ^ 2 > (a 1) ^ 2 := by nlinarith [h3, Real.sqrt_nonneg ((3 + a 1) / 2)]
      nlinarith [Real.sqrt_nonneg ((3 + a 1) / 2)]
    constructor <;> linarith
  · -- Assume 0 < a 1 ∧ a 1 < 3 / 2, prove ∀ n, 0 < n → a (n + 1) > a n
    rintro ⟨ha1_pos, ha1_lt_32⟩
    intro n hn
    have h4 : ∀ (n : ℕ), a (n + 2) > a (n + 1) := by
      intro n
      induction n with
      | zero =>
        have ha21 : a 2 > a 1 := by
          have h2 : a 2 = sqrt ((3 + a 1) / 2) := by
            specialize han 1
            norm_num at han ⊢
            linarith
          rw [h2]
          have h5 : (sqrt ((3 + a 1) / 2)) ^ 2 > (a 1) ^ 2 := by
            have h11 : (sqrt ((3 + a 1) / 2)) ^ 2 = (3 + a 1) / 2 := Real.sq_sqrt (by nlinarith [ha1_pos])
            have h12 : (3 + a 1) / 2 > (a 1) ^ 2 := by
              nlinarith
            nlinarith [Real.sqrt_nonneg ((3 + a 1) / 2)]
          have h6 : sqrt ((3 + a 1) / 2) > a 1 := by nlinarith [Real.sqrt_nonneg ((3 + a 1) / 2)]
          linarith
        simpa using ha21
      | succ n ih =>
        have h5 : a (n + 3) > a (n + 2) := by
          have h6 : a (n + 3) = sqrt ((3 + a (n + 2)) / 2) := by
            specialize han (n + 2)
            simpa using han
          have h7 : a (n + 2) = sqrt ((3 + a (n + 1)) / 2) := by
            specialize han (n + 1)
            simpa using han
          rw [h6]
          have h10 : a (n + 2) > a (n + 1) := ih
          have h11 : (3 + a (n + 2)) / 2 > (3 + a (n + 1)) / 2 := by linarith
          have h12 : sqrt ((3 + a (n + 2)) / 2) > sqrt ((3 + a (n + 1)) / 2) := by
            apply Real.sqrt_lt_sqrt
            all_goals
              nlinarith [show a (n + 1) ≥ 0 by
                have h7a : a (n + 1) > 0 := by
                  have h8 : a (1) > 0 := by linarith [ha1_pos]
                  -- need to prove a (n + 1) > 0 by induction
                  have h9 : ∀ (n : ℕ), a (n + 1) > 0 := by
                    intro n
                    induction n with
                    | zero => linarith [ha1_pos]
                    | succ n ih =>
                      have h10 : a (n + 2) = sqrt ((3 + a (n + 1)) / 2) := by
                        specialize han (n + 1)
                        simpa using han
                      have h11 : sqrt ((3 + a (n + 1)) / 2) > 0 := by
                        apply Real.sqrt_pos.mpr
                        nlinarith [ih]
                      rw [h10]
                      linarith [h11]
                  specialize h9 n
                  linarith
                nlinarith
              ]
          have h13 : sqrt ((3 + a (n + 1)) / 2) = a (n + 2) := by linarith [h7]
          nlinarith [h13, h12]
        simpa using h5
    have h9 : n > 0 := by linarith
    have h10 : n ≥ 1 := by linarith
    have h11 : n = n := rfl
    -- need to adjust index
    have h12 : a (n + 1) > a n := by
      have h13 : a ((n - 1) + 2) > a ((n - 1) + 1) := h4 (n - 1)
      have h14 : (n - 1) + 2 = n + 1 := by
        omega
      have h15 : (n - 1) + 1 = n := by
        omega
      rw [h14, h15] at h13
      linarith
    linarith [h12]