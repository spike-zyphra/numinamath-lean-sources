import Mathlib

/-
Let $a, b$ and $c$ be strictly positive real numbers such that $a^{2}+b^{2}+c^{2}=\frac{1}{2}$. Show that

$$
\frac{1-a^{2}+c^{2}}{c(a+2 b)}+\frac{1-b^{2}+a^{2}}{a(b+2 c)}+\frac{1-c^{2}+b^{2}}{b(c+2 a)} \geqslant 6
$$
-/
theorem inequalities_108741 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1 / 2) :
    6 ≤ (1 - a^2 + c^2) / (c * (a + 2 * b)) + (1 - b^2 + a^2) / (a * (b + 2 * c)) +
        (1 - c^2 + b^2) / (b * (c + 2 * a)) := by
  /- 
  We note that $1-a ^ {2}+c ^ {3}=2 \left (a ^ {3}+b ^ {3}+c ^ {3} \right) - a ^ {3}+c ^ {3}=a ^ {3}+2b ^ {3}+3c ^ {3} $. 
  On the other hand, according to the mean inequality, we have $a c \leqslant \frac {1} {2} \left (a ^ {2}+c ^ {3} \right) $and $2 b c \leqslant b ^ {3}+c ^ {3} $, therefore
  $$ 
  c(a+2 b)=a c+2 b c \leqslant \frac{1}{2}\left(a^{2}+c^{2}\right)+b^{2}+c^{2}=\frac{1}{2}\left(a^{2}+2 b^{2}+3 c^{2}\right) 
  $$
  From this, it can be inferred that 
  $$ 
  \frac{1-a^{2}+c^{2}}{c(a+2 b)} \geqslant \frac{a^{2}+2 b^{2}+3 c^{2}}{\frac{1}{2}\left(a^{2}+2 b^{2}+3 c^{2}\right)}=2 
  $$ 
  -/
  have h1 : (1 - a^2 + c^2) / (c * (a + 2 * b)) ≥ 2 := by
    have h1 : c * (a + 2 * b) > 0 := mul_pos (by linarith) (by nlinarith)
    have h2 : 1 - a^2 + c^2 - 2 * c * (a + 2 * b) ≥ 0 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - c)]

    -- 1 - a^2 + c^2 ≥ 2*c*(a + 2*b)
    have h3 : (1 - a^2 + c^2) / (c * (a + 2 * b)) - 2 ≥ 0 := by
      have h3 : (1 - a^2 + c^2) - 2 * (c * (a + 2 * b)) ≥ 0 := by linarith
      have h4 : (1 - a^2 + c^2) / (c * (a + 2 * b)) - 2 = ((1 - a^2 + c^2) - 2 * (c * (a + 2 * b))) / (c * (a + 2 * b)) := by
        field_simp
        ring
      rw [h4]
      apply div_nonneg
      · linarith
      · nlinarith
    simp [h3]
    linarith

  -- Similarly, we found $\frac{1-b^{2}+a^{2}}{a(b+2 c)} \geqslant 2$ and $\frac{1-c^{2}+b^{2}}{b(c+2 a)} \geqslant 2$.
  have h2 : (1 - b^2 + a^2) / (a * (b + 2 * c)) ≥ 2 := by
    have h1 : a * (b + 2 * c) > 0 := mul_pos (by linarith) (by nlinarith)
    have h2 : 1 - b^2 + a^2 - 2 * a * (b + 2 * c) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c)]
    have h3 : (1 - b^2 + a^2) / (a * (b + 2 * c)) - 2 ≥ 0 := by
      have h3 : (1 - b^2 + a^2) - 2 * (a * (b + 2 * c)) ≥ 0 := by linarith
      have h4 : (1 - b^2 + a^2) / (a * (b + 2 * c)) - 2 = ((1 - b^2 + a^2) - 2 * (a * (b + 2 * c))) / (a * (b + 2 * c)) := by
        field_simp
        ring
      rw [h4]
      apply div_nonneg
      · linarith
      · nlinarith
    simp [h3]
    linarith
  
  have h3 : (1 - c^2 + b^2) / (b * (c + 2 * a)) - 2 ≥ 0 := by
    have h1 : b * (c + 2 * a) > 0 := mul_pos (by linarith) (by nlinarith)
    have h2 : 1 - c^2 + b^2 - 2 * b * (c + 2 * a) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
    have h3 : (1 - c^2 + b^2) / (b * (c + 2 * a)) - 2 ≥ 0 := by
      have h3 : (1 - c^2 + b^2) - 2 * (b * (c + 2 * a)) ≥ 0 := by linarith
      have h4 : (1 - c^2 + b^2) / (b * (c + 2 * a)) - 2 = ((1 - c^2 + b^2) - 2 * (b * (c + 2 * a))) / (b * (c + 2 * a)) := by
        field_simp
        ring
      rw [h4]
      apply div_nonneg
      · linarith
      · nlinarith
    exact h3

  -- By adding these three terms together, we get the result.
  linarith