import Mathlib

/- Let $a_1,$ $a_2,$ $a_3,$ $\dots$ be an arithmetic sequence, and let $b_1,$ $b_2,$ $b_3,$ $\dots$ be a geometric sequence.  The sequence $c_1,$ $c_2,$ $c_3,$ $\dots$ has $c_n = a_n + b_n$ for each positive integer $n.$  If $c_1 = 1,$ $c_2 = 4,$ $c_3 = 15,$ and $c_4 = 2,$ compute $c_5.$ -/
theorem algebra_21695 (a b c : ℕ → ℝ)
    (h₀ : ∃ d, ∀ n, a n = a 0 + d * n)
    (h₁ : ∃ r, ∀ n, b n = b 0 * r ^ n)
    (h₂ : ∀ n, c n = a n + b n)
    (h₃ : c 0 = 1)
    (h₄ : c 1 = 4)
    (h₅ : c 2 = 15)
    (h₆ : c 3 = 2) :
    c 4 = 61 := by
  rcases h₀ with ⟨d, hd⟩
  rcases h₁ with ⟨r, hr⟩
  -- $a + b = 1$
  rw [h₂, hd, hr] at h₃
  simp only [CharP.cast_eq_zero, mul_zero, add_zero, pow_zero, mul_one] at h₃
  -- $a + d + br = 4$
  rw [h₂, hd, hr] at h₄
  simp only [Nat.cast_one, mul_one, pow_one] at h₄
  -- $a + 2d + br ^ 2 = 15$
  rw [h₂, hd, hr] at h₅
  simp only [Nat.cast_ofNat] at h₅
  -- $a + 3d + br ^ 3 = 2 $
  rw [h₂, hd, hr] at h₆
  simp only [Nat.cast_ofNat] at h₆
  -- Subtracting pairs of equations, we get:
  -- $d + br - b = 3$
  have h1 : d + b 0 * r - b 0 = 3 := by
    linarith
  -- $d + br ^ 2 - br = 11$
  have h2 : d + b 0 * r ^ 2 - b 0 * r = 11 := by
    linarith
  -- $d + br ^ 3 - br ^ 2 = -13$
  have h3 : d + b 0 * r ^ 3 - b 0 * r ^ 2 = -13 := by
    linarith
  -- Again subtracting pairs of equations, we get:
  -- $br ^ 2 - 2br + b = 8$
  have h4 : b 0 * r ^ 2 - 2 * b 0 * r + b 0 = 8 := by
    linarith
  -- $br ^ 3 - 2br ^ 2 + br = -24$
  have h5 : b 0 * r ^ 3 - 2 * b 0 * r ^ 2 + b 0 * r = -24 := by
    linarith
  -- We can write these as:
  -- $b(r - 1)^2 = 8
  have h6 : b 0 * (r - 1) ^ 2 = 8 := by
    linarith
  -- $br(r - 1)^2 = -24
  have h7 : b 0 * r * (r - 1) ^ 2 = -24 := by
    linarith
  -- Dividing these equations, we get $r = -3$
  have req : r = -3 := by
    rw [mul_comm (b 0), mul_assoc, h6] at h7
    linarith
  -- Then $16b = 8$, so $b = 1/2$
  have beq : b 0 = 1 / 2 := by
    rw [req] at h4
    linarith
  -- Solving for $a, d$, we find $a = 1 / 2$ and $d = 5$
  rw [req, beq] at h₄
  rw [beq] at h₃
  have aeq : a 0 = 1 / 2 := by
    linarith
  have deq : d = 5 := by
    linarith
  -- Hence $c_4 = 6$
  rw [h₂, hd, hr, aeq, deq, beq, req]
  norm_num