import Mathlib

/-If $f(c)=\frac{3}{2c-3}$, find $\frac{kn^2}{lm}$ when $f^{-1}(c)\times c \times f(c)$ equals the simplified fraction$\frac{kc+l}{mc+n}$, where $k,l,m,\text{ and }n$ are integers.-/
theorem algebra_19851 {f : ℝ → ℝ} (hf : ∀ c, f c = 3 / (2 * c - 3)) :
    ∃(k l m n : ℤ), Nat.Coprime (Int.gcd k l) (Int.gcd m n) ∧
      ∀c≠0, (Function.invFun f c) * c * f c = (k * c + l) / (m * c + n) ∧
      (k * n^2) / (l * m) = (9 : ℝ) := by
  -- Apply the definition of $f$ to the identity $f(f^{-1}(c))=c$ to find \begin{align*}
  -- c&=\frac{3}{2f^{-1}(c)-3}\quad\Rightarrow\\
  -- c(2f^{-1}(c)-3)&=3\quad\Rightarrow\\
  -- 2f^{-1}(c)-3&=\frac{3}{c}\quad\Rightarrow\\
  -- 2f^{-1}(c)&=\frac{3}{c}+3\quad\Rightarrow\\
  -- f^{-1}(c)&=\frac{3}{2c}+\frac{3}{2}\quad\Rightarrow\\
  -- &=\frac{3}{2}\left(\frac{1}{c}+1\right).
  -- \end{align*}
  have : Function.invFun f = fun c => 3 / (2 * c) + 3 / 2 := by
    ext c
    have : f (Function.invFun f c) = c := by
      apply Function.invFun_eq
      use (3 / (2 * c) + 3 / 2)
      rw [hf]
      ring_nf
      simp
    rw [hf] at this
    by_cases hc : c = 0
    · rw [hc]
      simp
      rw [hc] at this
      simp at this
      linarith
    have ne_zero : 2 * Function.invFun f c - 3 ≠ 0 := by
      by_contra! hp
      rw [hp] at this
      simp at this
      exact absurd this.symm hc
    rw [div_eq_iff ne_zero] at this
    have : (Function.invFun f c) * (2 * c) = 3 + 3 * c := by linarith
    rw [←eq_div_iff_mul_eq] at this
    rw [this]
    field_simp
    ring_nf
    -- Prove: 2 * c ≠ 0
    intro h
    simp at h
    exact absurd h hc
  rw [this, show f = fun c => 3 / (2 * c - 3) by funext c; rw [hf]]
  simp
  -- Therefore, $f^{-1}(c)\times c \times f(c)$ can be found: \begin{align*}
  -- f^{-1}(c)\times c \times f(c)&=\left(\frac{3}{2}\left(\frac{1}{c}+1\right)\right)\times c \times \frac{3}{2c-3}\quad\Rightarrow\\
  -- &=\frac{3}{2}\times\frac{1+c}{c}\times c \times\frac{3}{2c-3}\quad\Rightarrow\\
  -- &=\frac{3\times (1+c)\times 3}{2 \times (2c-3)}\quad\Rightarrow\\
  -- &=\frac{9+9c}{4c-6}\quad\Rightarrow\\
  -- &=\frac{9c+9}{4c-6}.
  -- \end{align*}Thus, $k=9$, $l=9$, $m=4$, and $n=-6$. So, $\frac{kn^2}{lm}=\frac{9\times(-6)^2}{9\times 4}=\boxed{9}$.
  use 9
  use 9
  use 4
  use -6
  use (by norm_num)
  intro c hc₀
  have : (3 / (2 * c) + 3 / 2) * c * (3 / (2 * c - 3)) = (9 * c + 9) / (4 * c - 6) := by
    ring_nf
    rw [mul_inv_cancel₀ hc₀]
    field_simp
    by_cases hc₁: c = 3/2
    · rw [hc₁]
      ring_nf
    rw [div_eq_div_iff]
    ring_nf
    -- Prove: (-3 + c * 2) * 2 ≠ 0
    intro h
    simp at h
    absurd hc₁
    linarith
    -- Prove: -6 + c * 4 ≠ 0
    intro h
    absurd hc₁
    linarith
  rw [this]
  use (by ring_nf)
  ring_nf
