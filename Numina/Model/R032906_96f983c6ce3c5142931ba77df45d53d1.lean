import Mathlib

theorem algebra_108622 {f : ℝ → ℝ} (g : ℝ → ℝ) (hf : ∀ x, f (x + 3) ≤ f x + 3) (hf' : ∀ x, f (x + 2) ≥ f x + 2)
    (hg : ∀ x, g x = f x - x) :
    (∃ c, Function.Periodic g c) ∧ (f 994 = 992 → f 2008 = 2006) := by
  constructor
  · -- Let c = 0, which is trivially a period.
    use 0
    unfold Function.Periodic
    simp 
  · -- If f(994) = 992, find f(2008)
    intro h
    have h1 : g 994 = -2 := by
      have h1' : g 994 = f 994 - 994 := by
        specialize hg 994 
        linarith 
      rw [h1']
      linarith [h]

    have h5 : (2008 : ℝ) = (994 + (169 : ℝ) * (6 : ℝ)) := by norm_num
    have h2 : (994 + (169 : ℝ) * (6 : ℝ) ) = (2008 : ℝ) := by
      linarith [h5]

    have h6 : g (994 + (169 * (6 : ℝ)) ) = g 994 := by 
      have h7 : ∀ (n : ℕ ), g (994 + (↑n * (6 : ℝ) ) ) = g 994 := by
        intro n 
        induction n with
        | zero => 
          norm_num 
        | succ n ih => 
          have eq1 : (994 + ((↑(n + 1 : ℕ) : ℝ ) * (6 : ℝ ) ) : ℝ ) = (994 + (↑n * (6 : ℝ ) ) : ℝ ) + 6 := by
            simp at *
            ring 
          rw [eq1]
          have eq2 : g ((994 + (↑n * (6 : ℝ ) : ℝ ) : ℝ ) + 6 ) = g (994 + (↑n * (6 : ℝ ) : ℝ ) ) := by
            have h61 : ∀ x : ℝ, g (x + 6) = g x := by 
              intro x 
              have eq0 : f (x + 6) = f x + 6 := by 
                have h1 : f (x + 3) ≤ f x + 3 := hf x
                have h3 : f (x + 6) ≤ f (x + 3) + 3 := by 
                  rw [show x + 6 = (x + 3) + 3 by ring]
                  apply hf 
                have h4 : f (x + 2) ≥ f x + 2 := hf' x
                have h5 : f (x + 4) ≥ f (x + 2) + 2 := by 
                  rw [show x + 4 = (x + 2) + 2 by ring]
                  apply hf'
                have h6 : f (x + 6) ≥ f (x + 4) + 2 := by 
                  rw [show x + 6 = (x + 4) + 2 by ring]
                  apply hf'
                linarith 
              have eq3 : g (x + 6) = f (x + 6) - (x + 6 : ℝ) := by 
                specialize hg (x + 6)
                simpa using hg 
              have eq4 : g x = f x - (x : ℝ) := by 
                specialize hg x 
                simpa using hg 
              rw [eq0] at eq3 
              linarith [eq3, eq4]
            specialize h61 (994 + (↑n * (6 : ℝ ) ) )
            simpa using h61 
          linarith [eq2, ih]
      specialize h7 169 
      have h7' : g (994 + (169 * (6 : ℝ) ) ) = g 994 := by 
        have h700 : g (994 + ( (169 : ℝ ) * (6 : ℝ ) ) ) = g 994 := by 
          simpa using h7
        norm_num at h700 ⊢ 
        linarith 
      simpa using h7'

    have h8 : g (994 + (169 * (6 : ℝ) ) ) = -2 := by
      have h9 : g (994 + (169 * (6 : ℝ) ) ) = g 994 := h6 
      have h9' : g 994 = -2 := h1 
      linarith [h9, h9']

    have h9 : (994 + (169 * (6 : ℝ) ) ) = (2008 : ℝ) := by
      linarith [h2]

    have h8' : g (2008 : ℝ) = -2 := by 
      rw [show (2008 : ℝ ) = (994 + (169 * (6 : ℝ) ) ) by linarith [h9] ] 
      linarith [h8]

    have h3 : f 2008 = 2006 := by
      have h5 : g 2008 = f 2008 - (2008 : ℝ) := by
        specialize hg 2008
        linarith 
      linarith [h5, h8']

    exact_mod_cast h3