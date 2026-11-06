import Mathlib
/- Solve the following equation for $x, y, z \in \mathbb{N}$

$$
\left(1+\frac{x}{y+z}\right)^{2}+\left(1+\frac{y}{z+x}\right)^{2}+\left(1+\frac{z}{x+y}\right)^{2}=\frac{27}{4}
$$ -/
theorem algebra_604467 (x y z : ℕ) : ((1 : ℝ) + x / (y + z)) ^ 2 + (1 + y / (z + x)) ^ 2 + (1 + z / (x + y)) ^ 2 = 27 / 4 ↔ (x = y ∧ y = z ∧ x ≠ 0):= by
  constructor
  .
    intro h
    rify
    -- Establish non-negativity of x, y, z
    have ha : x ≥ 0:= by omega
    have hb : y ≥ 0:= by omega
    have hc : z ≥ 0:= by omega
    rify at ha hb hc
    -- Convert natural numbers to reals
    set a:= (↑x : ℝ) with ha
    set b:= (↑y : ℝ) with hb
    set c:= (↑z : ℝ) with hc
    clear_value a b c
    clear ha hb hc x y z
    -- Prove that if the equation holds, none of a, b, c can be zero
    have h1 : ∀ a b c : ℝ, a ≥ 0 → b ≥ 0 → c ≥ 0 → (1 + a / (b + c)) ^ 2 + (1 + b / (c + a)) ^ 2 + (1 + c / (a + b)) ^ 2 = 27 / 4 → a ≠ 0:= by
      intro a b c ha hb hc h
      by_contra H
      subst a
      simp at h
      by_cases h1 : b = 0
      .
        subst b
        simp at h
        linarith
      .
        by_cases h2 : c = 0
        .
          subst c
          simp at h
          linarith
        .
          -- Use positivity to establish strict inequalities
          replace hb : b > 0:= by positivity
          replace hc : c > 0:= by positivity
          clear h1 h2
          -- Apply Cauchy-Schwarz inequality
          have h1 : (b / c - c / b) ^ 2 ≥ 0:= by positivity
          have h2 : b / c + c / b ≥ 2:= by
            field_simp
            have g1 : c * b > 0:= by positivity
            suffices 2 * (c * b) ≤ (b * b + c * c) / (c * b) * (c * b) by exact le_of_mul_le_mul_right this g1
            rw [show (b * b + c * c) / (c * b) * (c * b) = b * b + c * c by field_simp]
            have g2 : (b - c) ^ 2 ≥ 0:= by positivity
            linarith
          replace h2 : 2 + b / c + c / b ≥ 4:= by linarith
          replace h2 : (2 + b / c + c / b) ^ 2 ≥ 16:= by nlinarith only [h2]
          linarith

    -- Apply the previous result to all cyclic permutations
    have h2:= h1 a b c ha hb hc h
    have h3:= h1 b c a hb hc ha (by linarith)
    have h4:= h1 c a b hc ha hb (by linarith)
    -- Establish strict positivity
    replace ha : a > 0:= by positivity
    replace hb : b > 0:= by positivity
    replace hc : c > 0:= by positivity
    clear h1 h2 h3 h4
    -- Rewrite the equation using field operations
    rw [show (1 + a / (b + c)) ^ 2 + (1 + b / (c + a)) ^ 2 + (1 + c / (a + b)) ^ 2 = (a + b + c) ^ 2 * ((1 / (b + c)) ^ 2 + (1 / (c + a)) ^ 2 + (1 / (a + b)) ^ 2) by field_simp ; linarith] at h
    -- Apply Cauchy-Schwarz inequality in general form
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith
    -- Apply weighted Cauchy-Schwarz inequality
    replace h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2
        have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
        have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
        have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
        have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
        have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
        have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)
        have h1:= h1 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
        rw [g1, g2, g3, g4, g5, g6] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h1
        rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h1
        exact h1
    -- Establish non-negativity of squared differences
    have h2 : (a + b + c) ^ 2 * ((1 / (b + c) - 1 / (c + a)) ^ 2 + (1 / (c + a) - 1 / (a + b)) ^ 2 + (1 / (a + b) - 1 / (b + c)) ^ 2) ≥ 0:= by positivity
    specialize h1 1 1 1 (b + c) (c + a) (a + b) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    rw [show (1 ^ 2 / (b + c) + 1 ^ 2 / (c + a) + 1 ^ 2 / (a + b)) = 1 / (b + c) + 1 / (c + a) + 1 / (a + b) by simp] at h1
    rw [show (b + c + (c + a) + (a + b)) = 2 * (a + b + c) by ring] at h1
    rw [show ((1 : ℝ) + 1 + 1) ^ 2 = 9 by ring] at h1
    replace h1 : (a + b + c) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≥ 9 / 2:= by linarith
    replace h1 : ((a + b + c) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b))) ^ 2 ≥ 81 / 4:= by nlinarith only [h1]
    replace h2 : (a + b + c) ^ 2 * ((1 / (b + c) - 1 / (c + a)) ^ 2 + (1 / (c + a) - 1 / (a + b)) ^ 2 + (1 / (a + b) - 1 / (b + c)) ^ 2) = 0:= by linarith
    have h3 : a + b + c ≠ 0:= by positivity
    simp [h3] at h2
    -- Show that all reciprocal differences must be zero
    have g1 : (1 / (b + c) - 1 / (c + a)) ^ 2 ≥ 0:= by positivity
    have g2 : (1 / (c + a) - 1 / (a + b)) ^ 2 ≥ 0:= by positivity
    have g3 : (1 / (a + b) - 1 / (b + c)) ^ 2 ≥ 0:= by positivity
    simp at g1 g2 g3
    replace g1 : ((b + c)⁻¹ - (c + a)⁻¹) ^ 2 = 0:= by linarith
    replace g2 : ((c + a)⁻¹ - (a + b)⁻¹) ^ 2 = 0:= by linarith
    replace g3 : ((a + b)⁻¹ - (b + c)⁻¹) ^ 2 = 0:= by linarith
    simp at g1 g2 g3
    field_simp at g1 g2 g3
    have g4 : a ≠ 0:= by positivity
    simp [g4]
    constructor
    all_goals
    linarith
  .
    -- Prove the reverse direction: if x = y = z and x ≠ 0, then the equation holds
    intro h
    rcases h with ⟨h1, h2, h3⟩
    subst x y
    rify at h3
    field_simp
    linarith
