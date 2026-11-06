import Mathlib

theorem number_theory_189492 (x : ℕ → ℕ) (hx1 : x 1 = 2)
    (hxn : ∀ n, x (n + 1) = ⌊(1.5 : ℝ) * x n⌋) :
    {n | Odd (x n)}.Infinite ∧ {n | Even (x n)}.Infinite := by
  have h1 : x 1 = ⌊(1.5 : ℝ) * (x 0 : ℝ)⌋ := hxn 0
  rw [hx1] at h1
  -- Now, h1 : 2 = ⌊1.5 * ↑x 0⌋. This will lead to a contradiction.
  -- The right side is an integer.
  have h1' : (⌊(1.5 : ℝ) * (x 0 : ℝ)⌋ : ℤ) = (2 : ℤ) := by 
    norm_num at h1 ⊢
    omega
  -- Now, use the properties of the floor function.
  have h3 : (⌊(1.5 : ℝ) * (x 0 : ℝ)⌋ : ℤ) = (2 : ℤ) := h1'
  -- Now, we need to convert this equality into constraints on the value inside floor.
  have h4 : ( (2 : ℤ) ≤ (1.5 : ℝ) * (x 0 : ℝ) ) := by
    have h5 : ⌊(1.5 : ℝ) * (x 0 : ℝ)⌋ = (2 : ℤ) := by 
      omega
    have h6 : ( (⌊(1.5 : ℝ) * (x 0 : ℝ)⌋ : ℤ) ) = (2 : ℤ) := h5
    have h7 : ( (⌊(1.5 : ℝ) * (x 0 : ℝ)⌋ : ℤ) ) = (2 : ℤ) := h6
    rw [Int.floor_eq_iff] at h7
    exact_mod_cast h7.1
  -- Now, we need the upper bound from floor.
  have h9 : ( (1.5 : ℝ) * (x 0 : ℝ) ) < ( ( (2 : ℤ) + 1 ) : ℝ ) := by
    have h5 : ⌊(1.5 : ℝ) * (x 0 : ℝ)⌋ = (2 : ℤ) := by 
      omega
    have h6 : ( (⌊(1.5 : ℝ) * (x 0 : ℝ)⌋ : ℤ) ) = (2 : ℤ) := h5
    rw [Int.floor_eq_iff] at h6
    exact_mod_cast h6.2
  -- Now convert h9 into the original upper bound (3: ℝ)
  have h11 : ( (1.5 : ℝ) * (x 0 : ℝ) ) < ( (3 : ℝ) ) := by 
    have h11 : ( (1.5 : ℝ) * (x 0 : ℝ) ) < ( ( (2 : ℤ) + 1 ) : ℝ ) := h9
    norm_num at h11 ⊢
    linarith
  -- Now we have 2 of constraints.
  -- (2 : ℝ) ≤ 1.5 * ↑(x 0)
  -- (1.5 * ↑(x 0) ) < (3 : ℝ)
  -- These are impossible for a natural number x 0.
  -- Let's convert back to ℕ.
  -- lower bound
  have h12 : x 0 ≥ 2 := by
    by_contra h12
    push_neg at h12
    have h13 : x 0 < 2 := by omega
    have h14 : x 0 = 0 ∨ x 0 = 1 := by omega
    rcases h14 with (h14 | h14)
    · -- Assume x 0 = 0
      rw [show (x 0 : ℝ) = (0 : ℝ) by exact_mod_cast h14] at h4
      norm_num at h4
    · -- Assume x 0 = 1
      rw [show (x 0 : ℝ) = (1 : ℝ) by exact_mod_cast h14] at h4
      norm_num at h4
  -- Now, upper bound analysis.
  have h13 : x 0 < 2 := by
    by_contra h13
    push_neg at h13
    have h15 : x 0 ≥ 2 := by omega
    have h16 : (x 0 : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h15
    nlinarith
  -- contradiction: x 0 ≥ 2 and x 0 < 2
  linarith