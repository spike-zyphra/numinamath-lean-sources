import Mathlib
/- Let $a, b, c$ be positive real numbers for which $a+b+c=1$. Prove that

$$
\frac{a-b c}{a+b c}+\frac{b-c a}{b+c a}+\frac{c-a b}{c+a b} \leq \frac{3}{2} .
$$ -/
theorem algebra_605332 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) :
  (a - b * c) / (a + b * c) + (b - c * a) / (b + c * a) + (c - a * b) / (c + a * b) ≤ 3 / 2 := by
    -- First establish that 1-a, 1-b, 1-c are all positive
    have g1 : 1 - a > 0:= by linarith
    have g2 : 1 - b > 0:= by linarith
    have g3 : 1 - c > 0:= by linarith
    have g4 : (1 - a) * (1 - b) * (1 - c) > 0:= by positivity

    -- Transform each fraction by showing 1 minus each term equals 2bc/((1-b)(1-c)) etc.
    have h1 : 1 - (a - b * c) / (a + b * c) = 2 * b * c / ((1 - b) * (1 - c)):= by
      replace h : a = 1 - b - c:= by linarith
      rw [h]
      rw [show 1 - b - c + b * c = (1 - b) * (1 - c) by ring]
      field_simp
      linarith
    have h2 : 1 - (b - c * a) / (b + c * a) = 2 * c * a / ((1 - c) * (1 - a)):= by
      replace h : b = 1 - c - a:= by linarith
      rw [h]
      rw [show 1 - c - a + c * a = (1 - c) * (1 - a) by ring]
      field_simp
      linarith
    have h3 : 1 - (c - a * b) / (c + a * b) = 2 * a * b / ((1 - a) * (1 - b)):= by
      replace h : c = 1 - a - b:= by linarith
      rw [h]
      rw [show 1 - a - b + a * b = (1 - a) * (1 - b) by ring]
      field_simp
      linarith

    -- The problem reduces to proving the sum of these transformed terms ≥ 3/2
    suffices 2 * a * b / ((1 - a) * (1 - b)) + 2 * b * c / ((1 - b) * (1 - c)) + 2 * c * a / ((1 - c) * (1 - a)) ≥ 3 / 2 by linarith

    -- Multiply both sides by (1-a)(1-b)(1-c) to clear denominators
    suffices (2 * a * b / ((1 - a) * (1 - b)) + 2 * b * c / ((1 - b) * (1 - c)) + 2 * c * a / ((1 - c) * (1 - a))) * ((1 - a) * (1 - b) * (1 - c)) ≥ 3 / 2 * ((1 - a) * (1 - b) * (1 - c)) by exact le_of_mul_le_mul_right this g4
    clear h1 h2 h3

    -- Simplify the left side to 2(bc + ca + ab - 3abc)
    have h1 : (2 * a * b / ((1 - a) * (1 - b)) + 2 * b * c / ((1 - b) * (1 - c)) + 2 * c * a / ((1 - c) * (1 - a))) * ((1 - a) * (1 - b) * (1 - c)) = 2 * (b * c + c * a + a * b - 3 * a * b * c):= by
      field_simp
      ring
    rw [h1]

    -- Prove that bc + ca + ab ≥ 9abc using AM-GM inequality
    have h2 : b * c + c * a + a * b ≥ 9 * (a * b * c):= by
      have g5 : a * b * c > 0:= by positivity
      suffices (b * c + c * a + a * b) / (a * b * c) ≥ 9 by exact (le_div_iff₀ g5).mp this
      have g6 : (b * c + c * a + a * b) / (a * b * c) = 1 / a + 1 / b + 1 / c:= by
        field_simp
        linarith
      rw [g6]
      -- Use the fact that 1/x + 9x ≥ 6 for x > 0
      have g7 : ∀ x : ℝ, x > 0 → 1 / x + 9 * x ≥ 6:= by
        intro x hx
        suffices x * (1 / x + 9 * x) ≥ x * 6 by exact le_of_mul_le_mul_left this hx
        rw [show x * (1 / x + 9 * x) = 1 + 9 * x ^ 2 by field_simp; ring]
        suffices (3 * x - 1) ^ 2 ≥ 0 by linarith
        positivity
      have g8:= g7 b hb
      have g9:= g7 c hc
      replace g7:= g7 a ha
      linarith
    linarith
