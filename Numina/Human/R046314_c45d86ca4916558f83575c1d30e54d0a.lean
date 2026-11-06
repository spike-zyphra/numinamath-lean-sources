import Mathlib

/-Given that $x, y$ are real numbers, and $x+y=1$, find the maximum value of $\left(x^{3}+1\right)\left(y^{3}+1\right)$.-/
theorem algebra_603443 (x y : ℝ) (h : x + y = 1) :
    (x^3 + 1) * (y^3 + 1) ≤ 4 ∧ ∃ x y : ℝ, x + y = 1 ∧ (x^3 + 1) * (y^3 + 1) = 4 := by
  -- Since $x+y=1$, then 
  -- $\left(x^{3}+1\right)\left(y^{3}+1\right)=(x y)^{3}+x^{3}+y^{3}+1=(x y)^{3}+$ 
  -- $$\begin{array}{l} (x+y)\left(x^{2}-x y+y^{2}\right)+1=(x y)^{3}+(x+y)\left[(x+y)^{2}-3 x y\right]+1=(x y)^{3}- \ 3 x y+2=(x y-1)^{2}(x y+2)=\frac{1}{2}(1-x y)(1-x y)(2 x y+4) \leqslant \ \frac{1}{2}\left(\frac{(1-x y)+(1-x y)+2(x y+2)}{3}\right)^{3}=4 . \end{array}$$
  have h1 : (x^3 + 1) * (y^3 + 1) ≤ 4 := by
    have hy : y = 1 - x := by linarith
    rw [hy]
    nlinarith [sq_nonneg (x ^ 2 - x - 1), sq_nonneg (x ^ 2 - x + 2), sq_nonneg (x - (1 + Real.sqrt 5) / 2), sq_nonneg (x - (1 - Real.sqrt 5) / 2),
              Real.sq_sqrt (show (0 : ℝ) ≤ 5 from by norm_num)]
  have h2 : ∃ x y : ℝ, x + y = 1 ∧ (x^3 + 1) * (y^3 + 1) = 4 := by 
    -- When and only when $1-x y=2 x y+4$ and $x+y=1$, that is, 
    -- $x=\frac{1+\sqrt{5}}{2}, y=\frac{1-\sqrt{5}}{2}$ or $x=$ $\frac{1-\sqrt{5}}{2}, y=\frac{1+\sqrt{5}}{2}$, 
    -- $\left(x^{3}+1\right)\left(y^{3}+1\right)$ reaches its maximum value of 4.
    use (1 + Real.sqrt 5) / 2, (1 - Real.sqrt 5) / 2
    constructor
    · -- Prove x + y = 1
      ring
    · -- Prove (x^3 + 1) * (y^3 + 1) = 4
      have h1 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 := by
        have h1 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        ring_nf
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0)]
      have h2 : ((1 - Real.sqrt 5) / 2 : ℝ) ^ 2 = (1 - Real.sqrt 5) / 2 + 1 := by
        have h1 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        ring_nf
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0)]
      have h3 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 = 2 + Real.sqrt 5 := by
        have h1' : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 := h1
        calc
          ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3
              = ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 * ((1 + Real.sqrt 5) / 2) := by ring
          _ = ((1 + Real.sqrt 5) / 2 + 1) * ((1 + Real.sqrt 5) / 2) := by rw [h1']
          _ = (2 + Real.sqrt 5) := by
            ring_nf
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 from by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0)]
      have h4 : ((1 - Real.sqrt 5) / 2 : ℝ) ^ 3 = 2 - Real.sqrt 5 := by
        have h2' : ((1 - Real.sqrt 5) / 2 : ℝ) ^ 2 = (1 - Real.sqrt 5) / 2 + 1 := h2
        calc
          ((1 - Real.sqrt 5) / 2 : ℝ) ^ 3
              = ((1 - Real.sqrt 5) / 2 : ℝ) ^ 2 * ((1 - Real.sqrt 5) / 2) := by ring
          _ = ((1 - Real.sqrt 5) / 2 + 1) * ((1 - Real.sqrt 5) / 2) := by rw [h2']
          _ = (2 - Real.sqrt 5) := by
            ring_nf
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 from by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0)]
      have h5 : (((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 + 1) * (((1 - Real.sqrt 5) / 2 : ℝ) ^ 3 + 1) = 4 := by
        rw [h3, h4]
        ring_nf
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 from by norm_num)]
      linarith
  exact ⟨h1, h2⟩