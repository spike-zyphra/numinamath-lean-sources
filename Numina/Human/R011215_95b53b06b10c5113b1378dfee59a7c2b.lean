import Mathlib

/- 9. In the sequence $\left\{a_{n}\right\}$, $a_{4}=1, a_{11}=9$, and the sum of any three consecutive terms is 15. Then $a_{2016}=$ $\qquad$ -/
theorem algebra_231021 (a : ℕ → ℝ) (h₀ : a 4 = 1) (h₁ : a 11 = 9)
    (h₂ : ∀ n, a n + a (n + 1) + a (n + 2) = 15) :
    a 2016 = 5 := by
  -- Applying the consecutive sum property to different starting indices
  have eq1 := h₂ 2
  have eq2 := h₂ 3
  have eq3 := h₂ 4
  have eq4 := h₂ 5
  have eq5 := h₂ 6
  have eq6 := h₂ 7
  have eq7 := h₂ 8
  have eq8 := h₂ 9
  have eq9 := h₂ 10
  have eq10 := h₂ 11
  -- Simplifying the equations using the known value a₄=1
  norm_num [h₀] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10
  -- Proving that a₃=5 using linear arithmetic with our known values and equations
  have h3 : a 3 = 5 := by
    linarith [h₁, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10]
  -- Proving that the sequence has period 3: a(n+3) = a(n) for all n
  have h₃ : ∀ n, a (n + 3) = a n := by
    intro n
    have eq1 := h₂ n
    have eq2 := h₂ (n + 1)
    simp at eq1 eq2
    linarith
  -- Proving that a₂₀₁₆ = a₃ by using the periodicity property
  have h4 : a 2016 = a 3 := by
    -- Proving that a(3+3k) = a₃ for all natural numbers k
    have h : ∀ k : ℕ, a (3 + 3 * k) = a 3 := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        -- For the inductive step, we show that a(3+3(k+1)) = a(3+3k+3) = a(3+3k) = a₃
        have h1 : 3 + 3 * (k + 1) = (3 + 3 * k) + 3 := by ring
        rw [h1]
        have h2 := h₃ (3 + 3 * k)
        rw [h2]
        linarith [ih]
    -- Expressing 2016 as 3 + 3 * 671
    have h2016 : 2016 = 3 + 3 * 671 := by norm_num
    rw [h2016]
    exact h 671
  -- Concluding the proof by combining our results
  rw [h4, h3]
