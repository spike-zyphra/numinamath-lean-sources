import Mathlib

/- 5. Given positive numbers $a, b, c, d$ satisfy $a+2 b=1, c+2 d=1$, then the minimum value of $\frac{1}{a}+\frac{1}{b c d}$ is
A. $\frac{1}{16}$
B. 8
C. $\frac{1}{5}$
D. 25 -/
theorem algebra_127660 :
  IsLeast {x| ∃ (a b c d :ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a+2*b = 1 ∧ c + 2*d = 1 ∧ x = 1/a + 1/(b*c*d)} 25 := by
  constructor
    -- first show 25 is attainable by using 1/5, 2/5, 1/2, 1/4 for a, b, c, d
  . use 1/5, 2/5, 1/2, 1/4
    norm_num
    -- next prove 25 is a lower bound
  . rintro x ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd, hx⟩
    -- prove a version of am-gm ineq for 2 variables as that will be used
    have aux {p q : ℝ} (hp : 0 < p) (hq: 0 < q) : 4*p*q ≤ (p + q)^2 := by
      ring_nf
      have : 0 ≤ p^2 - p*q*2 + q^2 := by calc
        0 ≤ (p-q)^2 := by positivity
        _ = _ := by ring
      linarith
    -- using am-gm on c+2d=1, prove cd ≤ 1/8
    have : c*d ≤ 1/8 := by
      have := aux hc (by linarith : 0 < 2 * d)
      rw [hcd] at this
      linarith
    have : 1 / (c * d) ≥ 8 := by
      have := (inv_le_inv₀ (by norm_num: (1:ℝ)/8 > 0) (by positivity: c*d > 0)).mpr this
      simp; simp at this
      assumption
    -- thus 1/a + 8/b ≤ 1/a + 1/(bcd)
    have h₁ : 1/a + 8/b ≤ 1/a + 1/(b*c*d) := by calc
      1/a + 8/b ≤ 1/a + (1/(c*d))/b := by gcongr
      _ = 1/a + 1/(b*c*d) := by field_simp; ring
    -- next prove 25 ≤ 1/a + 1/b, to prove this utilize a+2b=1, in particular 25ab ≤ (a+2b)*(8a+b) is proven from (2a-b)^2 ≥ 0
    have h₂ : 25 ≤ 1/a + 8/b := by
      have : 0 ≤ (b - 2*a) ^2 := by positivity
      ring_nf at this
      have : 25 * a * b ≤ 8*a^2 + 17*a*b + 2*b^2 := by linarith
      calc
        25 = 25 * a * b / (a*b) := by field_simp; ring
        _ ≤ (8*a^2 + 17*a*b + 2*b^2)/(a*b)  := by gcongr
        _ = (8*a + b) * (a + 2*b) / (a*b) := by congr; ring_nf
        _ = 1/a + 8/b := by rw [hab]; field_simp; ring
    linarith