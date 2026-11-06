import Mathlib

open Real Set

/- 5 Let $u$, $v$, $w$ be positive real numbers, satisfying the condition

$$

u \sqrt{v w}+v \sqrt{w u}+w \sqrt{u v} \geqslant 1,

$$


Find the minimum value of $u+v+w$.
(Supplied by Chen Yonggao) -/
theorem inequalities_191212 :
    IsLeast {u + v + w | (u : ℝ) (v : ℝ) (w : ℝ) (_ : 0 < u) (_ : 0 < v) (_ : 0 < w)
    (_ : 1 ≤ u * √ (v * w) + v * √ (w * u) + w * √(u * v))} √3 := by
  constructor
  -- we provide √3/3 for u, v, w to show √3 is in the set
  . use √3/3, √3/3, √3/3
    simp
    and_intros
    . ring_nf
      simp
      rw [show 9 = (3: ℝ)^2 by ring]
      simp
      ring_nf
      simp
    . ring_nf
  -- next we prove √3 is a lower bound
  . simp
    rintro x ⟨u, v, w, h,  hu, hv, hw, hx⟩
    rw [← hx]
    clear x hx
    -- first of all we prove 1 ≤ uv + vw + wu, by utilizing am-gm on the squre roots
    have h1 : 1 ≤ u * v + v * w + w * u := by calc
      _ ≤ u * √ (v * w) + v * √ (w * u) + w * √(u * v) := by assumption
      _ ≤ u * ((v + w) / 2) + v * ((w + u) / 2) + w * ((u + v) / 2) := by
        gcongr
        all_goals rw [sqrt_mul (by positivity)]
        . have := two_mul_le_add_sq √v √w
          rw [sq_sqrt (by positivity), sq_sqrt (by positivity)] at this
          linarith
        . have := two_mul_le_add_sq √w √u
          rw [sq_sqrt (by positivity), sq_sqrt (by positivity)] at this
          linarith
        . have := two_mul_le_add_sq √u √v
          rw [sq_sqrt (by positivity), sq_sqrt (by positivity)] at this
          linarith
      _ = u * v + v * w + w * u := by ring
    -- now we'll prove square version of the inequality
    apply sq_le_sq₀ (by positivity) (by positivity) |>.mp
    simp
    -- we again use am-gm of 2 variables to prove 3 * (uv + vw + wu) ≤ (u + v + w)^3
    calc
      _ ≤ 3 * (u * v + v * w + w * u) := by linarith
      _ = u * v + v * w + w * u + 2 * u * v + 2 * v * w + 2 * w * u := by ring
      _ ≤ (u^2 + v^2) / 2 + (v^2 + w^2) / 2 + (w^2 + u^2) / 2 + 2 * u * v + 2 * v * w + 2 * w * u := by
        gcongr
        . linarith [two_mul_le_add_sq u v]
        . linarith [two_mul_le_add_sq v w]
        . linarith [two_mul_le_add_sq w u]
      _ = (u + v + w)^2 := by ring