import Mathlib

open Set Real

theorem inequalities_602797 (a : ℝ) (B : Set ℝ) (hB : B = {x | x^2 + (1 - a) * x - a < 0}) :
    B ⊆ {x | abs (x - 2) < 3} ↔ a ∈ Icc (-1) 5 := by
  constructor
  · -- Assume $B \subseteq \{x | abs (x - 2) < 3\}$, prove $a \in Icc (-1) 5$
    intro h
    have h1 : B ⊆ {x | abs (x - 2) < 3} := h
    have h2 : ∀ x : ℝ, x ∈ B → abs (x - 2) < 3 := by
      intro x hx
      apply h
      all_goals try { tauto }
    have h3 : ∀ x : ℝ, x ^ 2 + (1 - a) * x - a < 0 → abs (x - 2) < 3 := by
      intro x h4
      have hx : x ∈ B := by
        rw [hB]
        exact h4
      have h4' : abs (x - 2) < 3 := h2 x hx
      exact h4'
    -- Now we need to translate this to constraints on $a$
    have h4 : a ≥ -1 := by
      by_contra h
      push_neg at h
      have h5 : ( (a + (-1) ) / 2 ) ^ 2 + (1 - a) * ( (a + (-1) ) / 2 ) - a < 0 := by
        nlinarith [sq_nonneg ( (a + (-1) ) / 2 + 1 ), sq_nonneg ( (a + (-1) ) / 2 - a ) ]
      have h6 : abs ( ( (a + (-1) ) / 2 ) - 2 ) ≥ 3 := by
        have h9 : ( (a + (-1) ) / 2 ) - 2 < -3 := by
          nlinarith
        have h10 : abs ( ( (a + (-1) ) / 2 ) - 2 ) = - ( ( (a + (-1) ) / 2 ) - 2 ) := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        rw [h10]
        all_goals nlinarith
      have h5' : abs ( ( (a + (-1) ) / 2 ) - 2 ) < 3 := by
        apply h3 ( (a + (-1) ) / 2 ) h5
      linarith
    -- Now we need to prove $a \leq 5$
    have h6 : a ≤ 5 := by
      by_contra h
      push_neg at h
      have h7 : (5 + (a - 5)/2 ) ^ 2 + (1 - a) * (5 + (a - 5)/2 ) - a < 0 := by
        nlinarith [sq_nonneg ( (5 + (a - 5)/2 ) + 1 ), sq_nonneg ( (5 + (a - 5)/2 ) - a ) ]
      have h8 : abs ( (5 + (a - 5)/2 ) - 2 ) ≥ 3 := by
        have h9 : (5 + (a - 5)/2 ) - 2 ≥ 3 := by
          nlinarith
        have h10 : abs ( (5 + (a - 5)/2 ) - 2 ) = ( (5 + (a - 5)/2 ) - 2 ) := by
          rw [abs_of_nonneg]
          linarith
          all_goals linarith
        rw [h10]
        all_goals nlinarith
      have h8' : abs ( (5 + (a - 5)/2 ) - 2 ) < 3 := by
        apply h3 (5 + (a - 5)/2 ) h7
      linarith
    constructor <;> nlinarith
  · -- Assume $a \in Icc (-1) 5$, prove $B \subseteq \{x | abs (x - 2) < 3\}$
    rintro (⟨ha1, ha2⟩)
    intro x hx
    rw [hB] at hx
    have h1 : x ^ 2 + (1 - a) * x - a < 0 := by
      simpa using hx
    have h2 : -1 < x := by
      nlinarith [show x ^ 2 + (1 - a) * x - a = (x + 1) * (x - a) by ring, sq_nonneg (x + 1), sq_nonneg (x - a) ]
    have h3 : x < 5 := by
      nlinarith [show x ^ 2 + (1 - a) * x - a = (x + 1) * (x - a) by ring, sq_nonneg (x + 1), sq_nonneg (x - a) ]
    have h4 : abs (x - 2) < 3 := by
      rw [abs_lt]
      constructor <;> nlinarith
    exact h4