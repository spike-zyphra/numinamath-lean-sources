import Mathlib

/-Let the function $f(x) = x|x-a| + b$. Prove that: $f(x)$ is an odd function if and only if $a^2 + b^2 = 0$.-/
theorem algebra_9274 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x * abs (x - a) + b) :
    (∀ x : ℝ, f x = - f (-x)) ↔ a ^ 2 + b ^ 2 = 0 := by
  -- to prove the condition to be necessary and sufficient, we divide the problem into two parts.
  constructor
  intro h
  -- first we determine $b$ by plugging $x=0$ into the equation.
  have p₁: f 0 = 0 * |0 - a| + b := hf 0
  simp only [zero_sub, abs_neg, zero_mul, zero_add] at p₁
  -- by the property of odd functions, one would get $b=0$.
  have : f 0 = - f (-0) := h 0
  simp_rw [neg_zero, p₁] at this
  have b_sol: b = 0 := CharZero.eq_neg_self_iff.mp this
  -- now we determine $a$ by plugging $x=1$ into thhe equation and get $a=0$.
  have q₁: f 1 = 1 * |1 - a| + b := hf 1
  have q₂: f (-1) = - 1 * |- 1 - a| + b := hf (-1)
  simp_rw [one_mul, b_sol, add_zero] at q₁
  simp_rw [neg_mul, one_mul, b_sol, add_zero] at q₂
  have : f 1 = - f (-1) := h 1
  rw [q₁, q₂] at this; simp only [neg_neg] at this
  have k : (1 - a) ^ 2 = (-1 - a) ^ 2 := (sq_eq_sq_iff_abs_eq_abs (1 - a) (-1 - a)).mpr this
  have k₁ : (1 - a) ^ 2 = 1 - 2 * a + a ^ 2 := by ring
  have k₂ : (-1 - a) ^ 2 = 1 + 2 * a + a ^ 2 := by ring
  rw [k₁, k₂] at k; simp only [add_left_inj] at k
  have : a = 0 := by linarith
  -- plugging $a$ and $b$ into the equation and the desired result follows.
  rw [this, b_sol]; norm_num
  -- now we test the other side, which is merely a check of absolute value.
  intro h
  -- $a^2+b^2=0$ implies $a=0$ and $b=0$.
  have : a = 0 ∧ b = 0 := by
    refine mul_self_add_mul_self_eq_zero.mp ?_
    rw [← pow_two a, ← pow_two b, h]
  -- plugging $a=b=0$ and we get the desired result.
  rcases this with ⟨p₁, p₂⟩; rw [p₁, p₂] at hf; simp only [sub_zero, add_zero] at hf
  intro x; rw [hf, hf]; simp only [abs_neg, neg_mul, neg_neg]
