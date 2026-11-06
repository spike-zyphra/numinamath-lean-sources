import Mathlib
open Real
theorem algebra_326172 {a : ℕ → ℝ} (h : ∃ c, ∀ n, a n + a (n + 1) + a (n + 2) = c) (ha1 : a 2 = 9) (ha2 : a 6 = -7) (ha3 : a 97 = -1) : ∑ i in Finset.range 100, a i = 26:= by
  rcases h with ⟨c, hc⟩
  have h1 : ∀ n : ℕ, a n + a (n + 1) + a (n + 2) = c := hc
  have h2 : ∀ n : ℕ, a (n + 3) = a n := by
    intro n
    have eq1 : a n + a (n + 1) + a (n + 2) = c := hc n
    have eq2 : a (n + 1) + a (n + 2) + a (n + 3) = c := hc (n + 1)
    linarith
  have h3 : a 0 = -7 := by
    have h4 : a 6 = a 0 := by
      have h5 : a 6 = a 3 := by
        have h6 : a 6 = a 3 := by
          specialize h2 3
          rw [show 3 + 3 = (6 : ℕ) by omega] at h2
          linarith
        linarith
      have h7 : a 3 = a 0 := by
        specialize h2 0
        norm_num at h2
        linarith
      linarith
    linarith [ha2, h4]
  have h4 : a 1 = -1 := by
    have h5 : a 97 = a 1 := by
      have h6 : ∀ k : ℕ, a (3 * k + 1) = a 1 := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          have h8 : a (3 * (k + 1) + 1) = a (3 * k + 1) := by
            have h26 : a (3 * k + 1 + 3) = a (3 * k + 1) := by
              specialize h2 (3 * k + 1)
              simpa using h2
            have h29 : 3 * (k + 1) + 1 = (3 * k + 1) + 3 := by
              omega
            rw [h29]
            linarith [h26]
          rw [h8]
          all_goals linarith [ih]
      specialize h6 32
      simpa using h6
    linarith [ha3, h5]
  have h5 : c = 1 := by
    have h6 : a 0 + a 1 + a 2 = c := by
      specialize hc 0
      simpa using hc
    rw [show a 0 = -7 by linarith [h3], show a 1 = -1 by linarith [h4], show a 2 = 9 by linarith [ha1]] at h6
    linarith
  norm_num [Finset.sum_range_succ, h2, h3, h4, h5, ha1, ha2, ha3]