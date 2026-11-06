import Mathlib


lemma lemma_1
(a b : ℕ → ℝ)
(h1 : a 1 = -1)
(h2 : b 1 = 2)
(h3 : ∀ n, 0 < n → a (n + 1) = -b n ∧ b (n + 1) = 2 * a n - 3 * b n)
: ∀ n, 0 < n → b (n + 1) + b n = 3 * (-2)^n := by
  intro n hn
  have eq1 : ∀ n : ℕ, 0 < n → b (n + 1) + b n = 3 * (-2) ^ n := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        norm_num [h1, h2, h3] at *
      | succ n =>
        have eq3 : b ((n + 1 + 1) + 1) + b (n + 1 + 1) = -2 * (b (n + 1 + 1) + b (n + 1)) := by
          have eq4 : b ((n + 1 + 1) + 1) = 2 * a (n + 1 + 1) - 3 * b (n + 1 + 1) := by
            have h6 := (h3 (n + 1 + 1) (by linarith)).right
            linarith
          have eq5 : a (n + 1 + 1) = -b (n + 1) := by
            have h5 := (h3 (n + 1) (by linarith)).left
            linarith
          rw [eq4, eq5]
          ring
        have eq4 : b (n + 1 + 1) + b (n + 1) = 3 * (-2) ^ (n + 1) := by
          specialize ih (by linarith)
          simpa using ih
        rw [eq3, eq4]
        ring_nf
  specialize eq1 n hn
  simpa using eq1


theorem algebra_303329 {a b : ℕ → ℝ} (ha1 : a 1 = -1) (hb1 : b 1 = 2)
    (han : ∀ n > 0, a (n + 1) = -b n) (hbn : ∀ n > 0, b (n + 1) = 2 * a n - 3 * b n) :
    b 2015 + b 2016 = -3 * 2 ^ 2015 := by
  have h3 : ∀ n, 0 < n → a (n + 1) = -b n ∧ b (n + 1) = 2 * a n - 3 * b n := by
    intro n hn
    constructor
    . -- a (n + 1) = -b n
      apply han n hn
    . -- b (n + 1) = 2 * a n - 3 * b n
      apply hbn n hn

  have eq1 : ∀ n, 0 < n → b (n + 1) + b n = 3 * (-2)^n := lemma_1 a b ha1 hb1 h3

  have eq2 := eq1 2015 (by norm_num)
  norm_num [show (2015 + 1 : ℕ) = 2016 by omega] at eq2 ⊢
  linarith