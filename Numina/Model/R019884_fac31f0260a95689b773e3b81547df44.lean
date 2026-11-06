import Mathlib

open Finset

lemma lemma_1 (m c y x : ℕ) (hpos : 0 < m ∧ 0 < c ∧ 0 < y ∧ 0 < x ) (hm : m > c) (hy : y > x) : m ^ y > c * m ^ x := by
  rcases hpos with ⟨hm_pos, hc_pos, hy_pos, hx_pos⟩
  have h1 : y - x > 0 := by omega
  have h2 : m ^ y = m ^ x * m ^ (y - x) := by
    rw [← Nat.pow_add]
    have h3 : x + (y - x) = y := by
      omega
    rw [h3]
  have h3 : m ^ (y - x) > c := by
    have h4 : y - x ≥ 1 := by omega
    have h6 : m ^ (y - x) ≥ m := by
      have h7 : m ^ (y - x) ≥ m ^ 1 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals omega
      have h4 : m ^ 1 = m := by ring
      rw [h4] at h7
      linarith
    nlinarith [hm]
  rw [h2]
  nlinarith [h3, show m ^ x > 0 by positivity]


theorem inequalities_62017 {a b : ℕ → ℕ}
    (ha1 : a 1 = 2013)
    (han : ∀ n > 0, a (n + 1) = 2013 ^ a n)
    (hb1 : b 1 = 1)
    (hbn : ∀ n > 0, b (n + 1) = 2013 ^ (2012 * b n)) :
    ∀ n > 0, a n > b n := by
  intro n hn
  have h1 : ∀ n > 0, a n > b n := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      exact Nat.lt_irrefl 0 hn
    | succ n ih =>
      cases n with
      | zero =>
        rw [ha1, hb1]
        all_goals norm_num
      | succ n =>
        have h2 : a (n + 2) = 2013 ^ a (n + 1) := by
          specialize han (n + 1) (by omega)
          simpa using han
        have h3 : b (n + 2) = 2013 ^ (2012 * b (n + 1)) := by
          specialize hbn (n + 1) (by omega)
          simpa using hbn
        have h4 : a (n + 1) > b (n + 1) := by
          apply ih
          all_goals omega
        -- Show that $a_{n+2} > b_{n+2}$.
        -- We need to show that $2013^{a_{n+1}} > 2013^{2012 \cdot b_{n+1}}$.
        -- We need lemma 1.
        have h5 : a (n + 1) > 2012 * b (n + 1) := by
          have h2 : ∀ n : ℕ, a (n + 1) > 2012 * b (n + 1) := by
            intro n
            induction n with
            | zero =>
              rw [ha1, hb1]
              all_goals norm_num
            | succ n ih =>
              have h2 : a (n + 2) = 2013 ^ a (n + 1) := by
                specialize han (n + 1) (by omega)
                simpa using han
              have h3 : b (n + 2) = 2013 ^ (2012 * b (n + 1)) := by
                specialize hbn (n + 1) (by omega)
                simpa using hbn
              have h4 : a (n + 1) > 2012 * b (n + 1) := by
                apply ih
              -- Show that a_{n+2} > 2012 * b_{n+2}
              -- We need to show $2013^{a_{n+1}} > 2012 \cdot 2013^{2012 \cdot b_{n+1}}$
              -- Applying lemma 1 here.
              have h6 : 0 < 2013 := by norm_num
              have h7 : 0 < 2012 := by norm_num
              have h9 : 0 < a (n + 1) := by
                have h10 : a 1 = 2013 := ha1
                have : ∀ k > 0, a k > 0 := by
                  intro k hk
                  induction k with
                  | zero =>
                    exfalso
                    exact Nat.lt_irrefl 0 hk
                  | succ k ih =>
                    cases k with
                    | zero =>
                      simp [h10]
                    | succ k =>
                      have h14 : a (k + 2) = 2013 ^ a (k + 1) := by
                        specialize han (k + 1) (by omega)
                        simpa using han
                      have h15 : a (k + 1) > 0 := by
                        apply ih
                        all_goals omega
                      rw [h14]
                      all_goals positivity
                apply this (n + 1) (by omega)
              have h10 : 0 < 2012 * b (n + 1) := by
                have h11 : b (n + 1) > 0 := by
                  have h10 : b 1 = 1 := hb1
                  have : ∀ k > 0, b k > 0 := by
                    intro k hk
                    induction k with
                    | zero =>
                      exfalso
                      exact Nat.lt_irrefl 0 hk
                    | succ k ih =>
                      cases k with
                      | zero =>
                        simp [h10]
                      | succ k =>
                        have h14 : b (k + 2) = 2013 ^ (2012 * b (k + 1)) := by
                          specialize hbn (k + 1) (by omega)
                          simpa using hbn
                        have h15 : b (k + 1) > 0 := by
                          apply ih
                          all_goals omega
                        rw [h14]
                        all_goals positivity
                  apply this (n + 1) (by omega)
                have : 2012 * b (n + 1) > 0 := by
                  nlinarith
                omega
              have h11 : a (n + 2) > 2012 * b (n + 2) := by
                rw [h2, h3]
                have h12 : 2013 ^ a (n + 1) > 2012 * (2013 ^ (2012 * b (n + 1))) := by
                  apply lemma_1 (2013) 2012 (a (n + 1)) (2012 * b (n + 1))
                  all_goals
                    try omega
                    try positivity
                nlinarith
              linarith
          apply h2 n
        have h10 : a (n + 2) > b (n + 2) := by
          rw [h2, h3]
          have h11 : 2013 ^ a (n + 1) > 2013 ^ (2012 * b (n + 1)) := by
            have h12 : a (n + 1) > 2012 * b (n + 1) := h5
            have h9 : 2013 ^ a (n + 1) > 2013 ^ (2012 * b (n + 1)) := by
              apply Nat.pow_lt_pow_right
              all_goals
                try omega
                try nlinarith
            linarith
          linarith
        exact h10
  apply h1 n hn