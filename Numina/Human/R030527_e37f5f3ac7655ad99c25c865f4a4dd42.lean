import Mathlib

/-Trouver toutes les fonctions $f$ de $\mathbb{R}$ dans $\mathbb{R}$ telles que pour tout couple $(x, y)$ de réels :

$$
f(f(x))+f(f(y))=2 y+f(x-y)
$$-/
theorem algebra_607330 (f : ℝ → ℝ) : (∀ x y, f (f x) + f (f y) = 2 * y + f (x - y)) ↔
∀ x, f x = x := by
  constructor
  -- Plug in $x=y=0$ to feq and simplify the relation
  · intro feq; have f0 := feq 0 0; simp only [← two_mul, mul_zero, sub_self, zero_add] at f0
  -- Plug in $x=y$ to feq and simplify the relation
    have fx1 : ∀ x, 2 * f (f x) = 2 * x + f 0 := by
      intro x; specialize feq x x; simp only [← two_mul, sub_self] at feq; exact feq
  -- Plug in $y=0$ to feq and simplify the relation
    have fx2 : ∀ x, f (f x) = f x - f (f 0) := by
      intro x; specialize feq x 0; simp only [mul_zero, sub_zero, zero_add] at feq; nth_rw 2 [← feq]; ring
  -- Plug in fx2 to fx1 and simplify the relation and replace fx2 with this new relation
    replace fx2 : ∀ x, f x = x + f 0 := by
      intro x; specialize fx1 x; specialize fx2 x
      rw [fx2, mul_sub, f0, sub_eq_iff_eq_add, add_assoc, ← two_mul, ← mul_add] at fx1
      apply mul_left_cancel₀ at fx1; exact fx1; simp
  -- Plug in the new fx2 to f0 to show $f(0)=0$
    rw [fx2, ← sub_eq_zero] at f0; ring_nf at f0; 
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at f0
  -- Plug in f0 to fx2 to finish the goal
    simp only [f0, add_zero] at fx2; exact fx2
-- Conversely, it is straightforward to check $f(x)=x$ satisfies the functional equation in question
  intro h; simp only [h]; intros; ring
