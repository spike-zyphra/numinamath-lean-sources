import Mathlib

/- If $x, y, z$ are non-negative real numbers such that $x^{2}+y^{2}+z^{2}=x+y+z$, then show that:

$$
\frac{x+1}{\sqrt{x^{5}+x+1}}+\frac{y+1}{\sqrt{y^{5}+y+1}}+\frac{z+1}{\sqrt{z^{5}+z+1}} \geq 3
$$

When does the equality hold? -/
theorem algebra_605184 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x ^ 2 + y ^ 2 + z ^ 2 = x + y + z) :
  (x + 1) / √(x ^ 5 + x + 1) + (y + 1) / √(y ^ 5 + y + 1) + (z + 1) / √(z ^ 5 + z + 1) ≥ 3:= by
    -- Step 1: Factor the denominators using algebraic identities
    rw [show x ^ 5 + x + 1 = (x ^ 2 + x + 1) * (x ^ 3 - x ^ 2 + 1) by ring_nf]
    rw [show y ^ 5 + y + 1 = (y ^ 2 + y + 1) * (y ^ 3 - y ^ 2 + 1) by ring_nf]
    rw [show z ^ 5 + z + 1 = (z ^ 2 + z + 1) * (z ^ 3 - z ^ 2 + 1) by ring_nf]

    -- Step 2: Prove that x³ - x² + 1 > 0 for x ≥ 0
    have g1 : ∀ x : ℝ, x ≥ 0 → x ^ 3 - x ^ 2 + 1 > 0:= by
      intro x hx
      have g1 : x ^ 5 + x + 1 > 0:= by positivity
      have g2 : x ^ 2 + x + 1 > 0:= by positivity
      by_contra H
      simp at H
      replace H : -x ^ 3 + x ^ 2 - 1 ≥ 0:= by linarith
      replace H : (x ^ 2 + x + 1) * (-x ^ 3 + x ^ 2 - 1) ≥ 0:= by positivity
      linarith
    have g2:= g1 y hy
    have g3:= g1 z hz
    replace g1:= g1 x hx
    -- Step 3: Apply AM-GM inequality to simplify square roots in denominators
    have h1 : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → √(x * y) ≤ (x + y) / 2:= by
      intro x y hx hy
      have h1 : (√x - √y) ^ 2 ≥ 0:= by positivity
      ring_nf at h1
      rw [show √x ^ 2 = x by exact Real.sq_sqrt hx] at h1
      rw [show √y ^ 2 = y by exact Real.sq_sqrt hy] at h1
      rw [show √x * √y = √(x * y) by exact Eq.symm (Real.sqrt_mul' x hy)] at h1
      linarith
    have h2:= h1 (y ^ 2 + y + 1) (y ^ 3 - y ^ 2 + 1) (by positivity) (by linarith)
    have h3:= h1 (z ^ 2 + z + 1) (z ^ 3 - z ^ 2 + 1) (by positivity) (by linarith)
    replace h1:= h1 (x ^ 2 + x + 1) (x ^ 3 - x ^ 2 + 1) (by positivity) (by linarith)
    -- Step 4: Simplify expressions using algebraic manipulations
    rw [show (z ^ 2 + z + 1 + (z ^ 3 - z ^ 2 + 1)) / 2 = (z ^ 3 + z + 2) / 2 by linarith] at h3
    rw [show (y ^ 2 + y + 1 + (y ^ 3 - y ^ 2 + 1)) / 2 = (y ^ 3 + y + 2) / 2 by linarith] at h2
    rw [show (x ^ 2 + x + 1 + (x ^ 3 - x ^ 2 + 1)) / 2 = (x ^ 3 + x + 2) / 2 by linarith] at h1
    -- Step 5: Apply inequality for fractions with positive denominators
    have h4 : (x + 1) / √((x ^ 2 + x + 1) * (x ^ 3 - x ^ 2 + 1)) ≥ (x + 1) / ((x ^ 3 + x + 2) / 2):= div_le_div_of_nonneg_left (by linarith) (by ring_nf ; positivity) h1
    have h5 : (y + 1) / √((y ^ 2 + y + 1) * (y ^ 3 - y ^ 2 + 1)) ≥ (y + 1) / ((y ^ 3 + y + 2) / 2):= div_le_div_of_nonneg_left (by linarith) (by ring_nf ; positivity) h2
    have h6 : (z + 1) / √((z ^ 2 + z + 1) * (z ^ 3 - z ^ 2 + 1)) ≥ (z + 1) / ((z ^ 3 + z + 2) / 2):= div_le_div_of_nonneg_left (by linarith) (by ring_nf ; positivity) h3
    rw [show x ^ 3 + x + 2 = (x + 1) * (x ^ 2 - x + 2) by ring_nf] at h4
    rw [show y ^ 3 + y + 2 = (y + 1) * (y ^ 2 - y + 2) by ring_nf] at h5
    rw [show z ^ 3 + z + 2 = (z + 1) * (z ^ 2 - z + 2) by ring_nf] at h6
    -- Step 6: Prove that x² - x + 2 > 0 using perfect square completion
    have g4 : x ^ 2 - x + 2 > 0:= by
      have g1 : (x - 1 / 2) ^ 2 ≥ 0:= by positivity
      linarith
    have g5 : y ^ 2 - y + 2 > 0:= by
      have g2 : (y - 1 / 2) ^ 2 ≥ 0:= by positivity
      linarith
    have g6 : z ^ 2 - z + 2 > 0:= by
      have g3 : (z - 1 / 2) ^ 2 ≥ 0:= by positivity
      linarith
    rw [show (x + 1) / ((x + 1) * (x ^ 2 - x + 2) / 2) = 2 / (x ^ 2 - x + 2) by field_simp ; linarith] at h4
    rw [show (y + 1) / ((y + 1) * (y ^ 2 - y + 2) / 2) = 2 / (y ^ 2 - y + 2) by field_simp ; linarith] at h5
    rw [show (z + 1) / ((z + 1) * (z ^ 2 - z + 2) / 2) = 2 / (z ^ 2 - z + 2) by field_simp ; linarith] at h6
    suffices 2 / (x ^ 2 - x + 2) + 2 / (y ^ 2 - y + 2) + 2 / (z ^ 2 - z + 2) ≥ 3 by linarith
    rw [show 2 / (x ^ 2 - x + 2) + 2 / (y ^ 2 - y + 2) + 2 / (z ^ 2 - z + 2) = (1 / (x ^ 2 - x + 2) + 1 / (y ^ 2 - y + 2) + 1 / (z ^ 2 - z + 2)) * 2 by ring_nf]
    suffices 1 / (x ^ 2 - x + 2) + 1 / (y ^ 2 - y + 2) + 1 / (z ^ 2 - z + 2) ≥ 3 / 2 by linarith
    clear g1 g2 g3 h1 h2 h3 h4 h5 h6
    -- Step 7: Apply the inequality 1/x + 1/y + 1/z ≥ 9/(x+y+z) for positive x, y, z
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → 1 / x + 1 / y + 1 / z ≥ 9 / (x + y + z):= by
      intro x y z hx hy hz
      have h1 : x + y + z > 0:= by positivity
      suffices (1 / x + 1 / y + 1 / z) * (x + y + z) ≥ 9 by exact (div_le_iff₀ h1).mpr this
      rw [show (1 / x + 1 / y + 1 / z) * (x + y + z) = x / y + y / x + x / z + z / x + y / z + z / y + 3 by field_simp ; ring_nf]
      have h2 : ∀ a b : ℝ, a > 0 → b > 0 → a / b + b / a ≥ 2:= by
        intro a b ha hb
        have h2 : a / b + b / a - 2 = (a - b) ^ 2 / (a * b):= by field_simp ; ring_nf
        suffices (a - b) ^ 2 / (a * b) ≥ 0 by linarith
        positivity
      have g1:= h2 x y hx hy
      have g2:= h2 y z hy hz
      have g3:= h2 z x hz hx
      linarith
    specialize h1 (x ^ 2 - x + 2) (y ^ 2 - y + 2) (z ^ 2 - z + 2) g4 g5 g6
    -- Step 8: Complete the proof using the original condition x² + y² + z² = x + y + z
    rw [show (x ^ 2 - x + 2) + (y ^ 2 - y + 2) + (z ^ 2 - z + 2) = (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) + 6 by ring_nf] at h1
    rw [show (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) + 6 = 6 by rw [h] ; linarith] at h1
    linarith
