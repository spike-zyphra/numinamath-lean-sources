import Mathlib

theorem number_theory_157844 (f : ℕ → ℕ) (hf : StrictMono f)
    (hff : ∀ n, f (f n) < n + 1) :
    f = fun n => n := by
  have h1 : f 0 = 0 := by
    have h2 : f (f 0) < 1 := hff 0
    have h3 : f (f 0) = 0 := by
      linarith
    by_cases h4 : f 0 > 0
    · -- Since f 0 > 0, by strictMono f, we have f(f 0) > f(0)
      have h5 : f (f 0) > f 0 := by
        apply hf
        linarith
      linarith [show f 0 ≥ 0 from by omega, h3, h5]
    · -- f 0 ≤ 0, so f 0 = 0
      have h6 : f 0 ≤ 0 := by
        omega
      have h7 : f 0 = 0 := by
        omega
      exact h7

  have h2 : ∀ n, f n ≥ n := by
    intro n
    induction n with
    | zero =>
      have h3 : f 0 = 0 := h1
      omega
    | succ n ih =>
      have h3 : f n < f (n + 1) := by
        apply hf
        all_goals
        omega
      omega

  have h3 : ∀ n, f n ≤ n := by
    intro n
    by_contra h4
    push_neg at h4
    have h4' : f n > n := by linarith
    have h5 : f (f n) ≥ f n := by
      have h7 : f n > n := h4'
      have h6 : f (f n) > f n := by
        apply hf
        all_goals
        omega
      linarith
    have h6 : f (f n) < n + 1 := by
      apply hff
    have h7 : f n < n + 1 := by
      nlinarith [h6, h5]
    omega

  funext n
  have h8 : f n ≥ n := h2 n
  have h9 : f n ≤ n := h3 n
  linarith