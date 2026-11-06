import Mathlib
open Real

/- 
6. Let $\mathbf{R}$ denote the set of all real numbers. Find all functions $f: \mathbf{R} \rightarrow \mathbf{R}$ satisfying the condition


$$

f(x+y)=f(x) f(y) f(x y)

$$


for all $x, y$ in $\mathbf{R}$.
 -/
theorem algebra_126815 (f : ℝ → ℝ)
    (h : ∀ x y, f (x + y) = f x * f y * f (x * y)) :
    (∀ x, f x = 0) ∨ (∀ x, f x = 1) ∨ (∀ x, f x = -1) := by
  -- set x = y = 0 and factor the equation
  have eq :  (f 0 - 1) * (f 0 + 1) * f 0 = 0 := by calc
    _ = (f 0)^3 - f (0 + 0) := by rw [add_zero]; ring
    _ = 0 := by rw [h 0 0, mul_zero]; ring
  -- split on whether f 0 = 0
  rcases mul_eq_zero.mp eq with fl | f0
  -- if not then f 0 = ±1
  · right
    rw [mul_eq_zero] at fl
    set k := (f 1) * (f (-1))^2 with hk
    -- show ∀ x, f x ≠ 0 by setting y = -x
    have f_ne_zero : ∀ x, f x ≠ 0
    · intro x
      rw [←sub_self x, show x - x = x +- x by rfl, h x (-x)] at fl
      simp at fl
      have f_ne : f x * (f (-x) * f (-(x * x))) ≠ 0 := by rcases fl with f_ne' | f_ne' <;> linarith [f_ne']
      exact (mul_ne_zero_iff.mp f_ne).left
    -- set y = x - 1
    have fk : ∀ x, 1 = f x * f (-x) * f (-x) * k
    · intro x
      have hx1 := h 1 (x - 1)
      rw [add_sub_cancel, one_mul] at hx1
      rw [show x - 1 = x + -1 by rfl, h x (-1)] at hx1
      simp at hx1
      rw [show f 1 * (f x * f (-1) * f (-x)) * (f x * f (-1) * f (-x)) = f x * (f x * f (-x) * f (-x) * k) by rw [hk]; ring] at hx1
      conv_lhs at hx1 => rw [←mul_one (f x)]
      exact mul_left_cancel₀ (f_ne_zero x) hx1
    have k_ne_zero : k ≠ 0 := mul_ne_zero (f_ne_zero 1) (pow_ne_zero 2 (f_ne_zero (-1)))
    -- by taking -x instead, we show that (f x)^3 is constant
    have cube : ∀ x, (f x)^3 = 1 / k
    · intro x
      have fx1 := fk x
      have fx2 := fk (-x)
      rw [fx2] at fx1
      apply mul_right_cancel₀ k_ne_zero at fx1
      rw [neg_neg] at fx1 fx2
      conv_rhs at fx1 => rw [mul_assoc, mul_comm]
      apply mul_right_cancel₀ (f_ne_zero x) at fx1
      apply mul_left_cancel₀ (f_ne_zero (-x)) at fx1
      rw [←fx1] at fx2
      field_simp
      rw [fx2]
      ring
    have f_const : ∀ x, f x = f 0
    · intro x
      have odd_3 : Odd (3 : ℕ) := Nat.odd_iff.mpr rfl
      apply (Odd.strictMono_pow odd_3).injective
      dsimp only
      rw [cube x, cube 0]
    rcases fl with fpos | fneg
    -- if f 0 = 1 then f x = 1
    · left; intro x; rw [f_const]; linarith [fpos]
    -- if f 0 = -1 then f x = -1
    · right; intro x; rw [f_const]; linarith [fneg]
  -- if f 0 = 0 then we're done immediately by setting y = 0
  left
  intro x
  rw [←add_zero x, h x 0, f0, mul_zero, zero_mul]