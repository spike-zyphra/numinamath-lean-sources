import Mathlib

open Real Set
open scoped BigOperators

-- This lemma expresses sin(x) in terms of tan(x/2), under the assumption that cos(x/2) ≠ 0.
lemma lemma_1 (x : ℝ) (h : cos (x / 2) ≠ 0): sin x = 2 * tan (x / 2) / (1 + tan (x / 2) ^ 2) := by calc
  -- Rewrite sin x as sin(2 * (x/2))
  sin x = sin (2 * (x / 2)) := by ring_nf
  -- Apply the double-angle identity for sine
  _ = 2 * sin (x / 2) * cos (x / 2) := by rw [sin_two_mul]
  -- Express sin(x/2) in terms of tan(x/2): sin = tan * cos
  _ = 2 * (tan (x / 2) * cos (x / 2)) * cos (x / 2) := by rw [tan_mul_cos h]
  -- Simplify to get cos²(x/2) * tan(x/2)
  _ = 2 * tan (x / 2) * cos (x / 2) ^ 2 := by ring_nf
  -- Replace cos²(x/2) using the identity involving 1 + tan²
  _ = 2 * tan (x / 2) / (1 + tan (x / 2) ^ 2) := by rw [← inv_one_add_tan_sq h]; ring_nf

-- This lemma expresses cos(x) in terms of tan(x/2), under the assumption that cos(x/2) ≠ 0.
lemma lemma_2 (x : ℝ) (h : cos (x / 2) ≠ 0): cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  -- Use the double-angle identity for cosine
  have h1 : cos x = 2 * cos (x / 2) ^ 2 - 1 := by
    rw [show cos x = cos (2 * (x / 2)) by ring_nf]
    rw [cos_two_mul]
  rw [h1]
  rw [tan_eq_sin_div_cos]
  -- Use the Pythagorean identity to express sin² in terms of cos²
  have htan3 : sin (x / 2) ^ 2 = 1 - cos (x / 2) ^ 2 := by
    linarith [sin_sq_add_cos_sq (x / 2)]
  -- Field simplification to express everything in terms of tan(x/2)
  field_simp [h]
  nlinarith [htan3]

-- Part 1: show y lies in a symmetric interval around 4/3 determined by √7.
lemma lemma_3 {x y : ℝ} (hy : y = (2 - sin x)/(2 - cos x)):
    ((1/3) * (4 - sqrt 7) ≤ y ∧ y ≤ (1/3) * (4 + sqrt 7)) := by
  -- Case split: handle the singularity when cos(x/2) = 0
  cases Classical.em (cos (x / 2) = 0)
  case inl h =>
    -- x/2 = (2k + 1)π/2, so x = (2k + 1)π
    obtain ⟨k, hk⟩ : ∃ k : ℤ, x / 2 = (2 * k + 1) * π / 2 := Real.cos_eq_zero_iff.1 h
    have hx : x = (2 * k + 1) * π := by linarith
    -- sin(x) = 0 at these points
    have hsin : sin x = 0 := by
      apply sin_eq_zero_iff.2
      use 2 * k + 1
      simp [hx]
    rw [hy, hsin]
    -- cos(x) lies in [−1,1]
    have h1 : -1 ≤ cos x ∧ cos x ≤ 1 := by
      apply cos_mem_Icc
    apply And.intro
    · field_simp
      -- Compute lower bound
      apply (div_le_div_iff₀ (by linarith) (by linarith [cos_le_one x])).2
      nlinarith [sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sqrt_nonneg 7]
    · field_simp
      -- Compute upper bound
      apply (div_le_div_iff₀ (by linarith [cos_le_one x]) (by linarith)).2
      nlinarith [sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sqrt_nonneg 7]
  case inr hneq =>
    /- Let $y=\frac{2-\sin x}{2-\cos x}$, $\tan \frac{x}{2}=t$ (which is well-defined since cos(x/2) ≠ 0), then\[ y=\frac{2-\frac{2t}{1+t^2}}{2-\frac{1-t^2}{1+t^2}}=\frac{2t^2-2t+2}{3t^2+1} \] -/
    let t := tan (x / 2)
    suffices 1 / 3 * (4 - √7) ≤ y ∧ y ≤ 1 / 3 * (4 + √7) by simp_all
    have ht : 1 + t ^ 2 ≠ 0 := by nlinarith
    -- Express y in terms of t using lemmas 1 and 2
    have hy : y = (2 * t ^ 2 - 2 * t + 2) / (3 * t ^2 + 1) := by calc
      y = (2 - (2 * t) / (1 + t ^ 2)) / (2 - (1 - t ^ 2) / (1 + t ^ 2))
        := by simp [hy, t]; rw [lemma_1 x hneq]; rw [lemma_2 x hneq]
      _ = (1 + t ^ 2) * (2 - (2 * t) / (1 + t ^ 2)) / ((1 + t ^ 2) * (2 - (1 - t ^ 2) / (1 + t ^ 2)))
        := by rw [← mul_div_mul_left _ _ ht]
      _ = (2 * t ^ 2 - 2 * t + 2) / (3 * t ^2 + 1)
        := by rw [mul_sub, mul_div_cancel₀ _ ht, mul_sub, mul_div_cancel₀ _ ht]; ring_nf
    -- Eliminate denominators: cross-multiply the expression for y
    have :  (2 * t ^ 2 - 2 * t + 2) * 1 = y * (3 * t ^2 + 1) := by
      rw [← mul_eq_mul_of_div_eq_div _ _ (by simp) (show 3 * t ^2 + 1 ≠ 0 by nlinarith)]
      simp
      exact hy
    -- Rearranging gives $(3y-2)t^2+2t+y-2=0$.
    have h1 : (3 * y - 2) * (t * t) + 2 * t + (y - 2) = 0 := by linarith

    /- Since $t$ is a real number, we have
      \[ \Delta=4-4(3y-2)(y-2)=-4(3y^2-8y+3)\leq 0, \]
      \[ y^2-\frac{8}{3}y+1\leq 0, \]
      \[ \left(y-\frac{4-\sqrt{7}}{3}\right)\left(y-\frac{4+\sqrt{7}}{3}\right)\geq 0, \]
      \[ \frac{1}{3}(4-\sqrt{7})\leq y\leq \frac{1}{3}(4+\sqrt{7}). \]-/
    -- Compute discriminant of the quadratic; must be non-negative for real roots
    have h2 : discrim (3 * y - 2) 2 (y - 2) ≥ 0 := by
      rw [discrim_eq_sq_of_quadratic_eq_zero h1]
      nlinarith
    -- Rearranged discriminant inequality
    have h3 : -4 * (3 * y ^ 2 - 8 * y + 3) ≥ 0 := by
      simp [discrim] at h2
      linarith
    -- Factor the discriminant inequality
    have h4 : (y - 1 / 3 * (4 - √7)) * (y - 1 / 3 * (4 + √7)) ≤ 0 := by calc
      (y - 1 / 3 * (4 - √7)) * (y - 1 / 3 * (4 + √7))
      _ = y ^ 2 - 8 / 3 * y + 1 / 9 * (4 ^ 2  - √7 ^ 2)
        := by linarith
      _ ≤ 0
        := by rw[sq_sqrt (by simp)]; linarith [h3]
    -- Solve the resulting inequality
    rcases mul_nonpos_iff.1 h4 with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · exact And.intro (by linarith [h5]) (by linarith [h6])
    · have : - √7 < √7 := by simp
      linarith

lemma lemma_4 {a b c s x : ℝ} (ha : a < 0) (hs : s ≥ 0)
  (h1 : discrim a b c = s * s) (h2 : a * (x * x) + b * x + c ≥ 0) :
  (-b + s) / (2 * a) ≤ x ∧ x ≤ (-b - s) / (2 * a) := by

    suffices -s ≤ 2 * a * x + b ∧ 2 * a * x + b ≤ s by
      rw [div_le_iff_of_neg (by linarith), le_div_iff_of_neg (by linarith)]
      exact And.intro (by linarith) (by linarith)
    suffices (2 * a * x + b) ^ 2 ≤ b ^ 2 - 4 * a * c by
      apply abs_le_of_sq_le_sq' _ (by linarith)
      rw [pow_two s, ← h1]
      assumption
    nlinarith

/- 17. Prove:
(1) $\frac{1}{3}(4-\sqrt{7}) \leqslant \frac{2-\sin x}{2-\cos x} \leqslant \frac{1}{3}(4+\sqrt{7})$;
(2) $\frac{1}{3}(4-\sqrt{7}) \leqslant \frac{x^{2}+x \sin t+1}{x^{2}+x \cos t+1} \leqslant \frac{1}{3}(4+\sqrt{7})$. -/
theorem inequalities_110997 (x : ℝ) (t : ℝ) :
    ((1/3) * (4 - sqrt 7) ≤ (2 - sin x)/(2 - cos x) ∧
    (2 - sin x)/(2 - cos x) ≤ (1/3) * (4 + sqrt 7)) ∧
    ((1/3) * (4 - sqrt 7) ≤ (x^2 + x * sin t + 1)/(x^2 + x * cos t + 1) ∧
    (x^2 + x * sin t + 1) / (x^2 + x * cos t + 1) ≤ (1/3) * (4 + sqrt 7)) := by
    apply And.intro
    · -- use lemma 3 for part 1
      exact lemma_3 rfl
    · have h1 :  x ^ 2 + x * cos t + 1 ≠ 0 := by
        rw [pow_two, ← one_mul (x * x), mul_comm x (cos t)]
        apply quadratic_ne_zero_of_discrim_ne_sq
        intro s
        simp [discrim]
        nlinarith [cos_sq_le_one t]
      cases Classical.em (sin t = cos t)
      case inl heq =>
        -- When $\sin t=\cos t$, the left side $\leq$ middle $=1\leq$ right side.
        simp [heq, div_self h1]
        apply And.intro
        · field_simp
          nlinarith [sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sqrt_nonneg 7]
        · field_simp
          nlinarith [sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sqrt_nonneg 7]
      case inr hneq =>
        /- When $\sin t\neq \cos t$, let
        \[ y=\frac{x^2+x\sin t+1}{x^2+x\cos t+1} \] -/
        let y := (x ^ 2 + x * sin t + 1) / (x ^ 2 + x * cos t + 1)
        have h1 : y - 1 = (x * (sin t - cos t)) / (x ^ 2 + x * cos t + 1) := by calc
          y - 1
          _ = (x ^ 2 + x * sin t + 1) / (x ^ 2 + x * cos t + 1) - (x ^ 2 + x * cos t + 1) / (x ^ 2 + x * cos t + 1)
            := by simp [y, div_self h1]
          _ = (x * (sin t - cos t)) / (x ^ 2 + x * cos t + 1)
            := by ring
        -- Then $(y-1)x^2+(y\cos t-\sin t)x+y-1=0$ has real roots $x$.
        have h2 : (y - 1) * (x * x) + (y * cos t - sin t) * x + (y - 1) = 0 := by calc
          (y - 1) * (x * x) + (y * cos t - sin t) * x + (y - 1)
          _ =  (x * (sin t - cos t) * (x * x) + ((x ^ 2 + x * sin t + 1) * cos t - (x ^ 2 + x * cos t + 1) * sin t) * x + x * (sin t - cos t)) / (x ^ 2 + x * cos t + 1)
            := by rw [h1]; field_simp [y]
          _ = 0
            := by ring
        /-  Therefore, \[ \Delta=(y\cos t-\sin t)^2-4(y-1)^2\geq 0. \] -/
        have h3 : discrim (y - 1) (y * cos t - sin t) (y - 1) ≥ 0 := by
          rw [discrim_eq_sq_of_quadratic_eq_zero h2]
          nlinarith
        --  However, \[ \Delta=y^2(\cos^2 t-4)-y(\sin 2t-8)+\sin^2 t-4 \]
        have h4 : (cos t ^ 2 - 4) * (y * y) + (8 - 2 * sin t * cos t) * y + (sin t * sin t - 4) ≥ 0 := by
          simp [discrim] at h3
          nlinarith [h3]
        /- As an equation in $y$, it has roots:
        \[ y_1=\frac{2-\sin t}{2-\cos t}, y_2=\frac{2+\sin t}{2+\cos t}=\frac{2-\sin(\pi+t)}{2+\cos(\pi+t)}. \]-/
        let y1 := (2 - sin t) / (2 - cos t)
        let y2 := (2 + sin t) / (2 + cos t)
        have hcos : -1 ≤ cos t ∧ cos t ≤ 1 := by
          apply cos_mem_Icc
        have h5 : (cos t ^ 2 - 4) * (y1 * y1) + (8 - 2 * sin t * cos t) * y1 + (sin t * sin t - 4) = 0 := by
          simp [y1]
          have ht1 : 2 - cos t ≠ 0 := by linarith
          field_simp [ht1]
          ring_nf
        have h6 : (cos t ^ 2 - 4) * (y2 * y2) + (8 - 2 * sin t * cos t) * y2 + (sin t * sin t - 4) = 0 := by
          simp [y2]
          have ht1 : 2 + cos t ≠ 0 := by linarith
          field_simp [ht1]
          ring_nf
        -- Since the parabola opens downwards, $y$ lies between $y_1$ and $y_2$.
        -- Aiming to apply lemma 4, and since we don't know which of y1 an y2 is larger, we work with the roots $(-b \pm s) / (2 * a)$ instead, where s is the root of discriminant of the quadratic
        let a := (cos t ^ 2 - 4)
        let b := (8 - 2 * sin t * cos t)
        let s := abs (2 * (cos t ^ 2 - 4) * y1 + (8 - 2 * sin t * cos t))
        have hs : s ≥ 0 := by simp [s]
        have h7 : discrim a b (sin t * sin t - 4) = s * s := by
          rw [← pow_two s, discrim_eq_sq_of_quadratic_eq_zero h5]
          simp [s]
        have h8 : (-b + s) / (2 * a) ≤ y ∧ y ≤ (-b - s) / (2 * a) := lemma_4 (by simp [a]; nlinarith) hs h7 h4
        have h9 : y1 = (-b + s) / (2 * a) ∨ y1 = (-b - s) / (2 * a) :=
          (quadratic_eq_zero_iff (by simp [a]; nlinarith) h7 y1).1 h5
        have h10 : y2 = (-b + s) / (2 * a) ∨ y2 = (-b - s) / (2 * a) :=
          (quadratic_eq_zero_iff (by simp [a]; nlinarith) h7 y2).1 h6
        /- From part [1] of this problem, we know that $y_1$ and $y_2$ are both within $\frac{1}{3}(4-\sqrt{7})$ and $\frac{1}{3}(4+\sqrt{7})$, so
        \[ \frac{1}{3}(4-\sqrt{7})\leq y\leq \frac{1}{3}(4+\sqrt{7}). \]-/
        have h11 : (1/3) * (4 - sqrt 7) ≤ y1 ∧ y1 ≤ (1/3) * (4 + sqrt 7) := by
          exact lemma_3 rfl
        have h12 : (1/3) * (4 - sqrt 7) ≤ y2 ∧ y2 ≤ (1/3) * (4 + sqrt 7) := by
          apply lemma_3
          show y2 = (2 - sin (t + π)) / (2 - cos (t + π))
          simp [sin_add_pi, cos_add_pi]
        have h13 : y1 ≠ y2 := by
          intro heq
          simp [y1, y2] at heq
          apply mul_eq_mul_of_div_eq_div (2 - sin t) (2 + sin t) (by linarith) (by linarith) at heq
          field_simp at heq
          have heq : sin t = cos t := by linarith [heq]
          exact hneq heq
        cases h9
        case inl h9 =>
          have : y2 = (-b - s) / (2 * a) := by by_contra; simp_all
          exact And.intro (by linarith) (by linarith)
        case inr h9 =>
          have : y2 = (-b + s) / (2 * a) := by by_contra; simp_all
          exact And.intro (by linarith) (by linarith)