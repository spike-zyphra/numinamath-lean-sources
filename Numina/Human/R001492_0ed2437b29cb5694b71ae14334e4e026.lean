import Mathlib
/- 24. (THA 2) Let $a, b, c, d$ be nonnegative real numbers such that $a b+b c+$ $c d+d a=1$. Show that  $$ \frac{a^{3}}{b+c+d}+\frac{b^{3}}{a+c+d}+\frac{c^{3}}{a+b+d}+\frac{d^{3}}{a+b+c} \geq \frac{1}{3} $$  ![](h ttps://cdn.mathpix.com/cropped/2024_11_18_8e985d6b9c83aa3e9d0eg-262.jpg?height=62&width=1190&top_left_y=791&top_left_x=173) a function $f: \mathbb{Q}^{+} \rightarrow \mathbb{Q}^{+}$such that  $$ f(x f(y))=\frac{f(x)}{y}, \quad \text { for all } x, y \text { in } \mathbb{Q}^{+} $$ -/
theorem inequalities_24305 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a * b + b * c + c * d + d * a = 1) : a ^ 3 / (b + c + d) + b ^ 3 / (a + c + d) + c ^ 3 / (a + b + d) + d ^ 3 / (a + b + c) ≥ 1 / 3:= by
  -- Prove that b + c + d > 0 by contradiction
  -- If b + c + d ≤ 0, then since b,c,d ≥ 0, we must have b = c = d = 0, which contradicts the condition a*b + b*c + c*d + d*a = 1
  have g1 : b + c + d > 0:= by
    by_contra H
    simp at H
    replace hb : b = 0:= by linarith
    replace hc : c = 0:= by linarith
    replace hd : d = 0:= by linarith
    subst b c d
    simp at h

  -- Similarly prove that a + c + d > 0
  have g2 : a + c + d > 0:= by
    by_contra H
    simp at H
    replace ha : a = 0:= by linarith
    replace hc : c = 0:= by linarith
    replace hd : d = 0:= by linarith
    subst a c d
    simp at h

  -- Similarly prove that a + b + d > 0
  have g3 : a + b + d > 0:= by
    by_contra H
    simp at H
    replace ha : a = 0:= by linarith
    replace hb : b = 0:= by linarith
    replace hd : d = 0:= by linarith
    subst a b d
    simp at h

  -- Similarly prove that a + b + c > 0
  have g4 : a + b + c > 0:= by
    by_contra H
    simp at H
    replace ha : a = 0:= by linarith
    replace hb : b = 0:= by linarith
    replace hc : c = 0:= by linarith
    subst a b c
    simp at h

  -- Lemma 1: For nonnegative x1, x2 and positive y1, y2, we have:
  -- x1³/y1 + x2³/y2 ≥ (x1² + x2²)²/(x1*y1 + x2*y2)
  have h1 : ∀ x1 x2 y1 y2 : ℝ, x1 ≥ 0 → x2 ≥ 0 → y1 > 0 → y2 > 0 → x1 ^ 3 / y1 + x2 ^ 3 / y2 ≥ (x1 ^ 2 + x2 ^ 2) ^ 2 / (x1 * y1 + x2 * y2):= by
    intro x1 x2 y1 y2 hx1 hx2 hy1 hy2
    by_cases h1 : x1 = 0
    .
      subst x1
      simp
      by_cases h2 : x2 = 0
      .
        subst x2
        simp
      .
        replace hx2 : x2 > 0:= by positivity
        rw [show (x2 ^ 2) ^ 2 / (x2 * y2) = x2 ^ 3 / y2 by field_simp ; linarith]
    .
      replace hx1 : x1 > 0:= by positivity
      clear h1
      have g1 : x1 * y1 + x2 * y2 > 0:= by positivity
      suffices (x1 ^ 3 / y1 + x2 ^ 3 / y2) * (x1 * y1 + x2 * y2) ≥ (x1 ^ 2 + x2 ^ 2) ^ 2 by exact (div_le_iff₀ g1).mpr this
      rw [show x1 ^ 3 / y1 + x2 ^ 3 / y2 = (x1 ^ 3 * y2 + x2 ^ 3 * y1) / (y1 * y2) by field_simp]
      replace g1 : y1 * y2 > 0:= by positivity
      rw [show (x1 ^ 3 * y2 + x2 ^ 3 * y1) / (y1 * y2) * (x1 * y1 + x2 * y2) = (x1 ^ 3 * y2 + x2 ^ 3 * y1) * (x1 * y1 + x2 * y2) / (y1 * y2) by ring]
      suffices (x1 ^ 3 * y2 + x2 ^ 3 * y1) * (x1 * y1 + x2 * y2) ≥ (x1 ^ 2 + x2 ^ 2) ^ 2 * (y1 * y2) by exact (le_div_iff₀ g1).mpr this
      suffices x1 * x2 * (x1 * y2 - x2 * y1) ^ 2 ≥ 0 by linarith
      positivity

  -- Apply Lemma 1 to b, d and a+c+d, a+b+c
  have h2:= h1 b d (a + c + d) (a + b + c) (by positivity) (by positivity) (by positivity) (by positivity)
  -- Apply Lemma 1 to a, c and b+c+d, a+b+d
  replace h1:= h1 a c (b + c + d) (a + b + d) (by positivity) (by positivity) (by positivity) (by positivity)
  clear g1 g2 g3 g4

  -- Prove that b*(a+c+d) + d*(a+b+c) > 0
  have g1 : b * (a + c + d) + d * (a + b + c) > 0:= by
    by_contra H
    simp at H
    have g6 : b * d ≥ 0:= by positivity
    linarith

  -- Prove that a*(b+c+d) + c*(a+b+d) > 0
  have g2 : a * (b + c + d) + c * (a + b + d) > 0:= by
    by_contra H
    simp at H
    have g5 : a * c ≥ 0:= by positivity
    linarith

  -- Lemma 2: For nonnegative x1, x2 and positive y1, y2, we have:
  -- x1²/y1 + x2²/y2 ≥ (x1+x2)²/(y1+y2)
  have h3 : ∀ x1 x2 y1 y2 : ℝ, x1 ≥ 0 → x2 ≥ 0 → y1 > 0 → y2 > 0 → x1 ^ 2 / y1 + x2 ^ 2 / y2 ≥ (x1 + x2) ^ 2 / (y1 + y2):= by
    intro x1 x2 y1 y2 _ _ hy1 hy2
    suffices (x1 ^ 2 / y1 + x2 ^ 2 / y2) * (y1 + y2) ≥ (x1 + x2) ^ 2 by exact (div_le_iff₀ (by positivity)).mpr this
    rw [show x1 ^ 2 / y1 + x2 ^ 2 / y2 = (x1 ^ 2 * y2 + x2 ^ 2 * y1) / (y1 * y2) by field_simp]
    rw [show (x1 ^ 2 * y2 + x2 ^ 2 * y1) / (y1 * y2) * (y1 + y2) = (x1 ^ 2 * y2 + x2 ^ 2 * y1) * (y1 + y2) / (y1 * y2) by ring]
    suffices (x1 ^ 2 * y2 + x2 ^ 2 * y1) * (y1 + y2) ≥ (x1 + x2) ^ 2 * (y1 * y2) by exact (le_div_iff₀ (by positivity)).mpr this
    suffices (x1 * y2 - x2 * y1) ^ 2 ≥ 0 by linarith
    positivity

  -- Apply Lemma 2 to (a²+c²), (b²+d²) and their respective denominators
  replace h3:= h3 (a ^ 2 + c ^ 2) (b ^ 2 + d ^ 2) (a * (b + c + d) + c * (a + b + d)) (b * (a + c + d) + d * (a + b + c)) (by positivity) (by positivity) g2 g1

  -- Simplify the inequality to prove
  suffices (a ^ 2 + c ^ 2 + (b ^ 2 + d ^ 2)) ^ 2 / (a * (b + c + d) + c * (a + b + d) + (b * (a + c + d) + d * (a + b + c))) ≥ 1 / 3 by linarith
  clear g1 g2 h1 h2 h3

  -- Simplify the denominator
  rw [show a * (b + c + d) + c * (a + b + d) + (b * (a + c + d) + d * (a + b + c)) = 2 * (a * c + b * d) + 2 by linarith]
  have g1 : 2 * (a * c + b * d) + 2 > 0:= by positivity

  -- Continue simplifying the inequality
  suffices (a ^ 2 + c ^ 2 + (b ^ 2 + d ^ 2)) ^ 2 ≥ 1 / 3 * (2 * (a * c + b * d) + 2) by exact (le_div_iff₀ g1).mpr this

  -- Use the inequality 2*(a*c + b*d) ≤ a² + c² + b² + d²
  have g2 : 2 * (a * c + b * d) ≤ a ^ 2 + c ^ 2 + (b ^ 2 + d ^ 2):= by
    suffices (a - c) ^ 2 + (b - d) ^ 2 ≥ 0 by linarith
    positivity

  -- Further simplify the inequality
  suffices (a ^ 2 + c ^ 2 + (b ^ 2 + d ^ 2)) ^ 2 ≥ 1 / 3 * (a ^ 2 + c ^ 2 + (b ^ 2 + d ^ 2) + 2) by linarith

  -- Prove that a² + c² + b² + d² ≥ 1 using the condition a*b + b*c + c*d + d*a = 1
  have g3 : a ^ 2 + c ^ 2 + (b ^ 2 + d ^ 2) ≥ 1:= by
    rw [←h]
    suffices (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 ≥ 0 by linarith
    positivity

  -- Set t = a² + c² + b² + d² to simplify notation
  set t:= a ^ 2 + c ^ 2 + (b ^ 2 + d ^ 2)
  clear_value t

  -- Final step: prove that (3*t + 2)*(t - 1) ≥ 0
  suffices (3 * t + 2) * (t - 1) ≥ 0 by linarith
  have g4 : t - 1 ≥ 0:= by linarith
  positivity
