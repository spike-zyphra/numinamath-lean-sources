import Mathlib

/-- 8. Given real numbers $\alpha, \beta$
  satisfy $\alpha^{3}-3 \alpha^{2}+5 \alpha=1,
  \beta^{3}-3 \beta^{2}+5 \beta=5$, then $\alpha+\beta=2$. -/
theorem algebra_132825 (α β : ℝ) (h₁ : α^3-3*α^2+5*α=1) (h₂ : β^3-3*β^2+5*β=5) : α+β=2 := by
  -- We have $x^3 - 3x^2 + 5x = (x-1)^3 + 2(x-1) + 3$.
  have (x : ℝ) : x^3 - 3 * x^2 + 5 * x = (x-1)^3 + 2 * (x-1) + 3 := by ring
  --Hence $(\alpha-1)^3 + 2 (\alpha-1) +3 = 1, (\beta-1)^3 + 2(\beta-1) + 3 = 5$.
  rw[this] at h₁ h₂
  -- Note that $x^3 + 2x$ is monotonically increasing, hence injective.
  have : StrictMono (fun x : ℝ => x^3 + 2 * x) := by
    intro x y lt
    simp only [add_lt_add_iff_right]
    have : x^3 < y^3 := Odd.strictMono_pow ⟨1,rfl⟩ lt
    gcongr
  -- From the previous equations, we can derive that
  -- $(\alpha-1)^3 + 2 (\alpha-1) = -2 = (1 - \beta)^3 + 2 * (1-\beta)$.
  have eqα : (α - 1)^3 + 2 * (α - 1) = -2 := by linarith
  have eqβ : (1 - β)^3 + 2 * (1 - β) = -2 := by linarith
  -- Hence $\alpha-1 = 1-\beta$,
  have := this.injective $ eqα.trans eqβ.symm
  -- and $\alpha + \beta = 1 - \beta + 1 + \beta = 2$.
  convert_to ((α - 1) + 1) + β = 2
  · ring
  · rw[this]; ring