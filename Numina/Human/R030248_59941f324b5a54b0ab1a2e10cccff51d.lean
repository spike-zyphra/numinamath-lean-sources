import Mathlib

/-Suppose that there exist nonzero complex numbers $a,$ $b,$ $c,$ and $d$ such that $k$ is a root of both the equations $ax^3 + bx^2 + cx + d = 0$ and $bx^3 + cx^2 + dx + a = 0.$  Enter all possible values of $k,$ separated by commas.-/
theorem algebra_12087 {a b c d k : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d)
    (h7 : a * k ^ 3 + b * k ^ 2 + c * k + d = 0)
    (h8 : b * k ^ 3 + c * k ^ 2 + d * k + a = 0) :
    k = 1 ∨ k = -1 ∨ k = Complex.I ∨ k = -Complex.I := by

  -- We have that, h7: ak^3 + bk^2 + ck + d = 0, and, h8: bk^3 + ck^2 + dk + a = 0.
  -- Multiplying the first equation by k, we get ak^4 + bk^3 + ck^2 + dk = 0.
  have h7' : (a * k ^ 3 + b * k ^ 2 + c * k + d) * k = 0 := by rw [h7, zero_mul]
  ring_nf at h7'

  -- Subtracting the equation $bk^3 + ck^2 + dk + a = 0,$ we get $ak^4 = a.$
  have h9 : (a * k ^ 4 + k * d + k ^ 2 * c + k ^ 3 * b)
       - (b * k ^ 3 + c * k ^ 2 + d * k + a) + a = a * k ^ 4:= by ring_nf
  rw [h7', h8] at h9
  simp at h9

  -- Since $a$ is nonzero, $k^4 = 1.$
  have h9 : k ^ 4 = 1 := by exact (mul_eq_left₀ ha).mp (id (Eq.symm h9))
  -- Then $k^4 - 1 = 0,$ which factors as (k - 1)(k + 1)(k^2 + 1) = 0.
  have h9 : (k - 1) * (k + 1) * (k ^ 2 + 1) = 0 := by
    ring_nf
    rw [h9]
    simp
  have : (k ^ 2 + 1) = (k - Complex.I) * (k + Complex.I) := by
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  rw [this, ←mul_assoc] at h9
  -- This means $k$ is one of $1,$ $-1,$ $i,$ or $-i.$
  simp at h9
  rcases h9 with (((r₁ | r₂) | r₃) | r₄)
  . -- r₁: k - 1 = 0
    exact Or.inl (sub_eq_zero.mp r₁)
  . -- r₂: k + 1 = 0
    apply Or.inr
    exact Or.inl (Eq.symm (neg_eq_of_add_eq_zero_left r₂))
  . -- r₃: k^2 + 1 = 0
    apply Or.inr
    apply Or.inr
    exact Or.inl (sub_eq_zero.mp r₃)
  . -- r₄: k + i = 0
    apply Or.inr
    apply Or.inr
    exact Or.inr (eq_neg_of_add_eq_zero_left r₄)
