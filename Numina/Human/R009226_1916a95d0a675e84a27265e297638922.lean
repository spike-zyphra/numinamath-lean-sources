import Mathlib
/- Define $x \star y=\frac{\sqrt{x^{2}+3 x y+y^{2}-2 x-2 y+4}}{x y+4}$. Compute

$$
((\cdots((2007 \star 2006) \star 2005) \star \cdots) \star 1) .
$$ -/
theorem algebra_608205 (f : ℝ → ℝ → ℝ) (a : ℕ → ℝ) (hf : f = fun x y => √(x ^ 2 + 3 * x * y + y ^ 2 - 2 * x - 2 * y + 4) / (x * y + 4)) (ha : a 0 = f 2007 2006) (han : ∀ n : ℕ, n ≤ 2004 → a (n + 1) = f (a n) (2005 - n)) : a 2005 = √15 / 9:= by
  -- Lemma 1: For any x > -2, f(x,2) = 1/2
  have h1 : ∀ x : ℝ, x > -2 → f x 2 = 1 / 2:= by
    intro x hx
    simp [hf]
    replace hx : x * 2 + 4 > 0:= by linarith
    field_simp
    ring_nf
    rw [show 4 + x * 4 + x ^ 2 = (x + 2) ^ 2 by ring]
    replace hx : x + 2 ≥ 0:= by linarith
    rw [show √((x + 2) ^ 2) = x + 2 by exact Real.sqrt_sq hx]
    linarith
  -- Lemma 2: For positive x and y, f(x,y) > 0
  have h2 : ∀ x y : ℝ, x > 0 → y > 0 → f x y > 0:= by
    intro x y hx hy
    simp [hf]
    rw [show x ^ 2 + 3 * x * y + y ^ 2 - 2 * x - 2 * y + 4 = (x + y - 1) ^ 2 + 3 + x * y by ring]
    positivity
  -- Apply the recursive formula for n = 2004
  rw [han 2004 (by norm_num)]
  norm_num
  -- Apply the recursive formula for n = 2003
  rw [han 2003 (by norm_num)]
  norm_num
  -- Lemma 3: Prove that a(n) > 0 for all n ≤ 2004 by induction
  have h3 : ∀ n : ℕ, n ≤ 2004 → a n > 0:= by
    intro n
    induction n with
    | zero =>
      simp
      rw [ha]
      exact h2 _ _ (by norm_num) (by norm_num)
    | succ n ih =>
      intro h
      replace ih:= ih (by linarith)
      rw [han n (by linarith)]
      exact h2 _ _ ih (by rify at h ; linarith)
  -- Apply Lemma 1 to a(2003)
  rw [h1 (a 2003) (by linarith only [h3 2003 (by norm_num)])]
  simp [hf]
  norm_num
  field_simp
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  field_simp
  linarith
