import Mathlib

/-
Let $f$ be a function from the set of real numbers to itself that satisfies 
$$ f(x+y) \leq y f(x)+f(f(x)) $$  for all real numbers $x$ and $y$.
Prove that $f(x)=0$ for all $x \leq 0$.
-/

theorem algebra_24019 (f : ℝ → ℝ) (h : ∀ x y, f (x + y) ≤ y * f x + f (f x)) :
    ∀ x ≤ 0, f x = 0 := by
-- Substituting $y=t-x$, we rewrite (II) as  $$ f(t) \leq t f(x)-x f(x)+f(f(x)) .$$  (2)
  have h1 x t : f t ≤ t * f x - x * f x + f (f x) := by
    specialize h x (t - x)
    ring_nf at h ⊢
    simpa
-- Consider now some real numbers $a, b$. We will show that $$ 2 f(a) f(b) \geq a f(a)+b f(b) . $$.
  have h2 a b : 2 * f a * f b ≥ a * f a + b * f b := by
-- Use (2) with $t=f(a), x=b$ as well as with $t=f(b)$, $x=a$. We get  $$ \begin{aligned} & f(f(a))-f(f(b)) \leq f(a) f(b)-b f(b), \\ & f(f(b))-f(f(a)) \leq f(a) f(b)-a f(a) . \end{aligned} $$
    have c1 : f (f a) - f (f b) ≤ f a * f b - b * f b := by
      specialize h1 b (f a)
      linarith
    have c2 : f (f b) - f (f a) ≤ f a * f b - a * f a := by
      specialize h1 a (f b)
      linarith
-- Adding these two inequalities yields  $$ 2 f(a) f(b) \geq a f(a)+b f(b) . $$
    linarith
-- Now, substitute $b=2 f(a)$ to obtain $2 f(a) f(b) \geq a f(a)+2 f(a) f(b)$, or $a f(a) \leq 0$.
  have h3 a : a * f a ≤ 0 := by
    specialize h2 a (2 * f a)
    linarith
--So, we get  $$ f(a) \geq 0 \text { for all } a<0 \text {. } $$  (3)
  replace h3 a (ha : a < 0) : f a ≥ 0 := by
    specialize h3 a
    nlinarith
-- We now show $$ f(x) \leq 0 \quad \text { for all real } x $$
  have h4 : ∀ x, f x ≤ 0 := by
-- Suppose $f(x)>0$ for some real number $x$.
    by_contra h4
    push_neg at h4
    obtain ⟨x, hx⟩ := h4
-- From (2) we immediately get that for every $t<\frac{x f(x)-f(f(x))}{f(x)}$, we have $f(t)<0$.
    have c1 t (ht : t < (x * f x - f (f x)) / f x) : f t < 0 := by
      specialize h1 x t
      replace ht := (mul_lt_mul_iff_of_pos_right hx).mpr ht
      field_simp at ht
      linarith
-- This contradicts (3); therefore  $$ f(x) \leq 0 \quad \text { for all real } x $$
    let y := (x * f x - f (f x)) / f x
    let z := min (y - 1) (-1)
    have hz : z ≤ -1 := by apply min_le_right
    have hz2 : z ≤ y - 1 := by apply min_le_left
    specialize h3 z (by linarith)
    specialize c1 z (by linarith)
    linarith
-- and by (3) again we get $f(x)=0$ for all $x<0$.  (4)
  have h5 : ∀ x < 0, f x = 0 := by
    intro x hx
    specialize h3 x hx
    specialize h4 x
    linarith
-- We are left to find $f(0)$. Setting $t=x<0$ in (2) we get  $$ 0 \leq 0-0+f(0), $$  so $f(0) \geq 0$.
  have h6 : f 0 ≥ 0 := by
    specialize h1 (-1) (-1)
    specialize h5 (-1) (by norm_num)
    simpa [h5] using h1
-- Combining this with (4) we obtain $f(0)=0$.
  have h7 : f 0 = 0 := by
    specialize h4 0
    linarith
  intro x hx
  rcases (show x < 0 ∨ x = 0 from lt_or_eq_of_le hx) with hx | hx
  . exact h5 x hx
  . subst hx
    exact h7
