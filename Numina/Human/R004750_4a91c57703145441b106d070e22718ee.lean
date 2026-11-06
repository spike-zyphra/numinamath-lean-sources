import Mathlib
/-3. If $\frac{a+b}{c}=\frac{b+c}{a}=\frac{c+a}{b}=k$, then the graph of the line $y=k x+k$ must pass through ( ).
(A) the first, second, and third quadrants
(B) the second and third quadrants
(C) the second, third, and fourth quadrants
(D) none of the above-/
theorem algebra_316350 (a b c k : ℝ) 
  (h1 : (a + b) / c = k)
  (h2 : (b + c) / a = k)
  (h3 : (c + a) / b = k)
  (hc : c ≠ 0)
  (ha : a ≠ 0) 
  (hb : b ≠ 0) :
  k = -1 ∨ k = 2 := by
  -- Step 1: Clear the denominators, converting the fractional equations to linear equations
  field_simp [hc, ha, hb] at h1 h2 h3 ⊢
  -- Now h1 : a + b = k * c, h2 : b + c = k * a, h3 : c + a = k * b
  -- Step 2: Add the three equations to get 2(a + b + c) = k(a + b + c)
  have h_sum : 2 * (a + b + c) = k * (a + b + c) := by
    nlinarith [h1, h2, h3]
  -- Step 3: Case analysis on a + b + c = 0 or a + b + c ≠ 0
  cases' eq_or_ne (a + b + c) 0 with h h
  · -- Case 1: a + b + c = 0
    -- Substitute into h_sum to get 0 = k * 0, so k can be any value, but further constraints are needed
    have : k = -1 := by
      have hn: a + b = -c := by linarith
      rw [hn] at h1
      apply mul_left_cancel₀ hc
    -- Convert the equation to `-c - k * c = 0`, i.e., `c(-1 - k) = 0`
      linarith
    exact Or.inl this
  · -- Case 2: a + b + c ≠ 0
    -- Cancel out the common factor to get k = 2
    have : k = 2 := by
      apply mul_left_cancel₀ h
      nlinarith
    exact Or.inr this
