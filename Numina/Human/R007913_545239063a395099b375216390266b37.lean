import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- Let $z_21552 = 18 + 83i$, $z_21552 = 18 + 39i,$ and $z_21552 = 78 + 99i,$ where $i^2 = -1$. Let $z$ be the unique complex number with the properties that $\frac{z_21552 - z_1}{z_21552 - z_1} \cdot \frac{z - z_2}{z - z_3}$ is a real number and the imaginary part of $z$ is the greatest possible. Find the real part of $z$. -/
theorem algebra_21552 {z1 z2 z3 : ℂ}
  (hz1 : z1 = 18 + 83 * .I) (hz2 : z2 = 18 + 39 * .I) (hz3 : z3 = 78 + 99 * .I)
  (z : ℂ) (g : z ≠ z3) (hz : ∃ r : ℝ, (z3 - z1) / (z2 - z1) * (z - z2) / (z - z3) = r)
  (hzz : ∀ z' : ℂ, (∃ r : ℝ, (z3 - z1) / (z2 - z1) * (z' - z2) / (z' - z3) = r) →
    z'.im ≤ z.im) :
  z.re = 56 := by
    subst z1 z2 z3
    rcases hz with ⟨r, hz⟩
    have h1 : ((78 + 99 * I - (18 + 83 * I)) / (18 + 39 * I - (18 + 83 * I)) * (z - (18 + 39 * I)) / (z - (78 + 99 * I))).im = (↑r : ℂ).im:= by rw [hz]
    norm_num at h1
    -- 令 z = a + b * i
    let a:= z.re
    let b:= z.im
    have ha : a = z.re:= by rfl
    have hb : b = z.im:= by rfl
    have h2 : z = ↑(z.re) + ↑(z.im) * I:= by exact Eq.symm (re_add_im z)
    rw [←ha, ←hb] at h2
    rw [h2] at h1 g
    rw [←ha]
    rw [←hb] at hzz
    clear_value a b
    clear ha hb h2 hz z
    -- 展开分式
    simp [Complex.div_im, normSq] at h1
    norm_num at h1
    rw [show 78 + 99 * I - (18 + 83 * I) = 60 + 16 * I by ring_nf] at h1
    rw [show 39 * I - 83 * I = -44 * I by ring_nf] at h1
    simp [Complex.div_re] at h1
    norm_num at h1
    -- 约掉分母
    have _ : (a - 78) * (a - 78) + (b - 99) * (b - 99) ≠ 0:= by
      by_contra!
      have g1 : (a - 78) ^ 2 ≥ 0:= by positivity
      have g2 : (b - 99) ^ 2 ≥ 0:= by positivity
      replace g1 : (a - 78) ^ 2 = 0:= by linarith
      replace g2 : (b - 99) ^ 2 = 0:= by linarith
      replace g1 : (a - 78) = 0:= by exact pow_eq_zero g1
      replace g2 : (b - 99) = 0:= by exact pow_eq_zero g2
      replace g1 : a = 78:= by linarith
      replace g2 : b = 99:= by linarith
      have g3 : ↑a + ↑b * I = 78 + 99 * I:= by
        rw [g1, g2]
        norm_num
      trivial
    field_simp at h1
    -- 得到简化表达式
    replace h1 : (a - 56) ^ 2 + (b - 61) ^ 2 = 1928:= by linarith
    specialize hzz (56 + (61 + √1928) * I)
    have gz : ∀ z : ℂ, z.im = 0 → ∃ r : ℝ, z = ↑r:= by
      intro z tz
      use z.re
      rw [show z = z.re + (z.im) * I by exact Eq.symm (re_add_im z)]
      rw [tz]
      norm_num
    -- 证明 (b - 61) ^ 2 ≥ 1928
    have h2 : ((78 + 99 * I - (18 + 83 * I)) / (18 + 39 * I - (18 + 83 * I)) * (56 + (61 + ↑√1928) * I - (18 + 39 * I)) /
        (56 + (61 + ↑√1928) * I - (78 + 99 * I))).im = 0:= by
          simp [Complex.div_im, normSq, Complex.div_re]
          norm_num
          ring_nf
          rw [show √1928 ^ 2 = 1928 by refine sq_sqrt (by linarith)]
          linarith
    have h3 := gz ((78 + 99 * I - (18 + 83 * I)) / (18 + 39 * I - (18 + 83 * I)) * (56 + (61 + ↑√1928) * I - (18 + 39 * I)) /
        (56 + (61 + ↑√1928) * I - (78 + 99 * I)))
    replace h3 := h3 h2
    replace hzz := hzz h3
    clear h2 h3
    norm_num at hzz
    replace hzz : b - 61 ≥ √1928:= by linarith
    have h2 : √1928 ≥ 0:= by positivity
    replace hzz : (b - 61) ^ 2 ≥ √1928 ^ 2:= by nlinarith only [h2, hzz]
    rw [show √1928 ^ 2 = 1928 by refine sq_sqrt (by linarith)] at hzz
    have h3 : (a - 56) ^ 2 ≥ 0:= by positivity
    replace h3 : (a - 56) ^ 2 = 0:= by linarith
    replace h3 : a - 56 = 0:= by exact pow_eq_zero h3
    linarith
