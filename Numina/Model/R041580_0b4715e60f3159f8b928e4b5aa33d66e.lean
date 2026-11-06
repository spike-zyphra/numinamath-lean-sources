import Mathlib

theorem algebra_178575 {a b c α β γ : ℤ} (h₀ : a^2 + b^2 = c^2) (h₁ : α^2 + β^2 - γ^2 = 2)
    (s : ℤ) (hs : s = a * α + b * β - c * γ) (p q r : ℤ)
    (hp : p = a - α * s) (hq : q = b - β * s) (hr : r = c - γ * s) :
    p^2 + q^2 = r^2 := by
  rw [hp, hq, hr]
  rw [hs]
  nlinarith [sq_nonneg (a * β - b * α), sq_nonneg (a * γ - c * α), sq_nonneg (b * γ - c * β),
            sq_nonneg (a * α + b * β - c * γ), sq_nonneg (a * γ + b * β * c - c * (a * α + b * β)),
            sq_nonneg (a * β - b * α), sq_nonneg (a * γ - c * α), sq_nonneg (b * γ - c * β),
            h₀, h₁, 
            mul_self_nonneg (a * α), mul_self_nonneg (a * β), mul_self_nonneg (a * γ),
            mul_self_nonneg (b * α), mul_self_nonneg (b * β), mul_self_nonneg (b * γ),
            mul_self_nonneg (c * α), mul_self_nonneg (c * β), mul_self_nonneg (c * γ)]