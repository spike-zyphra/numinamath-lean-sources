import Mathlib

theorem number_theory_238524 (x y : ℤ) : x^3 = y^3 + 2 * y^2 + 1 ↔ (x = -2 ∧ y = -3) ∨ (x = 1 ∧ y = -2) ∨ (x = 1 ∧ y = 0) := by
  constructor
  · -- Forward: if $x^3 = y^3 + 2y^2 + 1$ then $(x,y)$ is one of the solutions
    intro h
    have h1 : x^3 = y^3 + 2 * y^2 + 1 := by linarith
    have h3 : x > y := by
      by_contra h4
      push_neg at h4
      have h4' : x ≤ y := by nlinarith
      have h5 : x^3 ≤ y^3 := by
        have h6 : x ≤ y := by linarith
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y), sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg ((x - y) * (x + y))]
      nlinarith [show x^3 = y^3 + 2 * y^2 + 1 by linarith [h1]]
    -- We now prove that $y$ must be in the range $-3 \leq y \leq 1$.
    have h6 : y ≤ 1 := by
      by_contra h7
      push_neg at h7
      have h7' : y ≥ 2 := by omega
      have h8 : x = y + 1 := by
        have h9 : x ≤ y + 1 := by
          nlinarith [sq_nonneg (x - (y + 1)), sq_nonneg (y + 1), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg ((x - y) * (x - (y + 1)))]
        have h10 : x ≥ y + 1 := by
          nlinarith [sq_nonneg (x - (y + 1)), sq_nonneg (y + 1), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg ((x - y) * (x - (y + 1)))]
        linarith
      rw [show x = y + 1 by linarith [h8]] at h1
      nlinarith [sq_nonneg (y - 0), sq_nonneg (y - (-3)), sq_nonneg ((y + 1) ^ 2), sq_nonneg (y ^ 2), sq_nonneg ((y + 1) * y)]
    -- We now prove that $y \geq -3$.
    have h5 : y ≥ -3 := by
      by_contra h8
      push_neg at h8
      have h8' : y ≤ -4 := by omega
      have h9 : x ≤ y + 1 := by
        nlinarith [sq_nonneg (x - (y + 1)), sq_nonneg (y + 1), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg ((x - y) * (x - (y + 1)))]
      have h10 : x ≥ y + 2 := by
        nlinarith [sq_nonneg (x - y - 1), sq_nonneg (y + 1), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg ((x - y) * (x - (y + 1)))]
      -- This is impossible, so $y \geq -3$.
      have h11 : x = y + 2 := by
        linarith
      rw [show x = y + 2 by linarith [h11]] at h1
      nlinarith [sq_nonneg (y + 3), sq_nonneg (y * (y + 1)), sq_nonneg ((y + 1) * (y + 2)), sq_nonneg (y * (y + 1)), sq_nonneg ((y + 3) * (y + 2))]
    -- Now use `interval_cases` on $y$.
    have h7 : y ≤ 1 := by linarith [h6]
    have h8 : y ≥ -3 := by linarith [h5]
    interval_cases y <;> try { 
      have h9 : x ≤ 2 := by
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x * 1), sq_nonneg ((x - 1) * (x - 1)), sq_nonneg ((x + 2) ^ 2)]
      have h10 : x ≥ -2 := by
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x * 1), sq_nonneg ((x - 1) * (x - 1)), sq_nonneg ((x + 2) ^ 2)]
      interval_cases x <;> omega 
    }
    <;> try { 
      omega 
    }
    <;> try { 
      exfalso 
      <;> try { 
        nlinarith 
      } 
    }
    <;> omega
  · -- Backward: each pair $(x,y)$ satisfies the equation
    rintro (h | h | h)
    · -- Case $(-2, -3)$
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case $(1, -2)$
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case $(1, 0)$
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num