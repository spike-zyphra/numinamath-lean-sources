import Mathlib

theorem algebra_298981 {f : ℝ → ℝ} (hf1 : ∀ x, f (x + 3) ≤ f x + 3)
    (hf2 : ∀ x, f (x + 2) ≥ f x + 2) :
    (∃ c, Function.Periodic (fun x => f x - x) c) ∧ (f 998 = 1002 → f 2000 = 2004) := by
  constructor
  · -- Show that exists c, such that g(x) = f(x) - x is periodic with period c
    use 0
    unfold Function.Periodic
    simp
  · -- Show that if f(998) = 1002 then f(2000) = 2004
    intro h
    have h1 : ∀ x, f (x + 6) = f x + 6 := by
      intro x
      have h2 : f (x + 6) ≤ f x + 6 := by
        have h3 : f (x + 3) ≤ f x + 3 := hf1 x
        have h4 : f (x + 6) ≤ f (x + 3) + 3 := by
          rw [show x + 6 = (x + 3) + 3 by ring]
          apply hf1
        linarith
      -- Now get the lower bound
      have h5 : f (x + 6) ≥ f x + 6 := by
        have h6 : f (x + 2) ≥ f x + 2 := hf2 x
        have h7 : f (x + 4) ≥ f (x + 2) + 2 := by
          rw [show x + 4 = (x + 2) + 2 by ring]
          apply hf2
        have h8 : f (x + 6) ≥ f (x + 4) + 2 := by
          rw [show x + 6 = (x + 4) + 2 by ring]
          apply hf2
        linarith
      linarith
    -- We need to show f(2000) = 2004 given f(998) = 1002
    -- The difference is 2000 - 998 = 1002
    -- And since f(x + 6) = f(x) + 6, so we need to compute k such that 998 + 6k = 2000
    -- Therefore k = (2000 - 998)/6 = 1002/6 = 167
    have h3 : ∀ k : ℕ, f (998 + (↑k * 6 : ℝ)) = 1002 + (↑k * 6 : ℝ) := by
      intro k
      induction k with
      | zero =>
        norm_num [h]
      | succ k ih =>
        have eq1 : (998 + ((↑(k + 1 : ℕ) : ℝ) * 6 : ℝ) ) = (998 + (↑k * 6 : ℝ) ) + (6 : ℝ) := by
          simp at *
          <;> ring_nf <;> norm_num
        rw [eq1]
        have eq2 : f ((998 + (↑k * 6 : ℝ) ) + (6 : ℝ) ) = f (998 + (↑k * 6 : ℝ) ) + 6 := by
          specialize h1 (998 + (↑k * 6 : ℝ) )
          simpa using h1
        rw [eq2]
        linarith [ih]
    specialize h3 167
    norm_num at h3 ⊢
    linarith