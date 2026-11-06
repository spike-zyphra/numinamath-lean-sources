import Mathlib

/- 2. let $a, b, c \in \mathbb{R}$ with $a, b, c \geq 1$. Show that holds:


$$

\min \left(\frac{10 a^{2}-5 a+1}{b^{2}-5 b+10}, \frac{10 b^{2}-5 b+1}{c^{2}-5 c+10}, \frac{10 c^{2}-5 c+1}{a^{2}-5 a+10}\right) \leq a b c

$$


## Solution: -/
theorem inequalities_264161 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    min (min ((10 * a^2 - 5 * a + 1) / (b^2 - 5 * b + 10)) ((10 * b^2 - 5 * b + 1) / (c^2 - 5 * c + 10))) ((10 * c^2 - 5 * c + 1) / (a^2 - 5 * a + 10)) ≤ a * b * c := by
  -- let f(x) = 10 * x^2 - 5 * x + 1
  set f : ℝ → ℝ := fun x => 10 * x^2 - 5 * x + 1
  -- let g(x) = x^2 - 5 * x + 10
  set g : ℝ → ℝ := fun x => x^2 - 5 * x + 10
  -- we have to prove that f a / g b ⊓ f b / g c ⊓ f c / g a ≤ a * b * c
  change f a / g b ⊓ f b / g c ⊓ f c / g a ≤ a * b * c
  -- show that 0 < f x for all x
  have ineq1 (x : ℝ) : 0 < f x := calc
    0 < 10 * (x - 1 / 4) ^ 2 + 3 / 8 := by positivity
    _ = 10 * x ^ 2 - 5 * x + 1 := by ring
  -- show that 0 < g x for all x
  have ineq2 (x : ℝ) : 0 < g x := calc
    0 < (x - 5 / 2) ^ 2 + (10 - 25 / 4) := by positivity
    _ = x^2 - 5 * x + 10 := by ring
  -- it follows that 0 ≤ f x / g y for all x and y
  have ineq3 (x y : ℝ) : 0 ≤ f x / g y := le_of_lt (div_pos (ineq1 x) (ineq2 y))
  -- prove the following inequality: f x / g x ≤ x^3 for 1 ≤ x
  have ineq {x : ℝ} (hx : 1 ≤ x) : f x / g x ≤ x^3 := by
    -- it is enought to show that f x ≤ x^3 * g x or 0 ≤ x^3 * g x - f x
    apply div_le_of_le_mul₀ (le_of_lt (ineq2 x)) (pow_nonneg (by linarith) 3)
    -- x^3 * g x - f x = (x - 1) ^ 5
    rw [←sub_nonneg, show x ^ 3 * (x ^ 2 - 5 * x + 10) - (10 * x ^ 2 - 5 * x + 1) = (x - 1) ^ 5 by ring]
    -- 0 ≤ (x - 1) ^ 5 for 1 ≤ x
    apply pow_nonneg (by linarith)
  -- prove that x ⊓ y ⊓ z ≤ r for non-negative x, y, z if x * y * z ≤ r ^ 3
  have min_ineq {x y z r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x * y * z ≤ r ^ 3) : x ⊓ y ⊓ z ≤ r := by
    -- 0 ≤ r because 0 ≤ x * y * z ≤ r ^ 3
    have hr : 0 ≤ r := by
      rw [←Odd.pow_nonneg_iff (show Odd 3 by decide)]
      apply le_trans _ h
      positivity
    -- it is enough to show that (x ⊓ y ⊓ z) ^ 3 ≤ r ^ 3
    apply le_of_pow_le_pow_left₀ (show 3 ≠ 0 by norm_num) hr
    apply le_trans _ h
    rw [pow_three, ←mul_assoc]
    -- we have x ⊓ y ⊓ z ≤ x, x ⊓ y ⊓ z ≤ y, and x ⊓ y ⊓ z ≤ z,
    -- so (x ⊓ y ⊓ z) ^ 3 ≤ x * y * z ≤ r ^ 3
    gcongr <;> simp_all
  -- apply min_ineq and get the following goal
  -- f a / g b * (f b / g c) * (f c / g a) ≤ (a * b * c) ^ 3
  apply min_ineq (ineq3 a b) (ineq3 b c) (ineq3 c a)
  -- we have
  -- f a / g b * (f b / g c) * (f c / g a)
  --          = (f a / g a) * (f b / g b) * (f c / g c)
  --          ≤ a^3 * b^3 * c^3 (from ineq)
  --          = (a * b * c) ^ 3
  calc
    f a / g b * (f b / g c) * (f c / g a) = (f a / g a) * (f b / g b) * (f c / g c) := by ring
    _ ≤ a ^ 3 * b ^ 3 * c ^ 3 := by gcongr <;> tauto
    _ = (a * b * c) ^ 3 := by ring