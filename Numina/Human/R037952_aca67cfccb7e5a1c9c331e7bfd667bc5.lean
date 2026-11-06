import Mathlib

/- Example 11. Find a fractional-linear function that maps the point $z_{1}$ to the point $w_{1}=0$, and the point $z_{2}$ to the point $w_{2}=\infty$. -/
theorem algebra_147153 {z₁ z₂ : ℂ} {div : ℂ → ℂ → WithTop ℂ} (hz1 : z₁ ≠ z₂)
  (hd : div = fun a b ↦ if b = 0 then ⊤ else ↑(a / b)) :
  ∃ a b c d,
  let f := fun z ↦ div (a * z + b) (c * z + d)
  f z₁ = 0 ∧ f z₂ = ⊤ :=
  -- use the function (z - z₁) / (z - z₂)
  ⟨1, -z₁, 1, -z₂, by simp [hd]; exact sub_ne_zero_of_ne hz1⟩