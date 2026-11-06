import Mathlib

/-Solve the inequality with respect to $x$: $a^{2}x-6 \lt 4x+3a$.-/
theorem algebra_9343 (a : ℝ) (x : ℝ) :
    a^2 * x - 6 < 4 * x + 3 * a ↔ ((x < 3 / (a - 2) ∧ (a > 2 ∨ a < -2)) ∨ (x > 3 / (a - 2) ∧ (a > -2 ∧ a < 2)) ∨ (True ∧ a = 2) ∨ (False ∧ a = - 2)) := by
  -- to solve the inequality we divide the problem into two parts: getting the desired solution and verify they are correct.
  constructor
  intro h
  -- notice that the inequality can be rewriten into easier form $(a+2)(a-2)x<3(a+2)$.
  have : (a + 2) * (a - 2) * x < 3 * (a + 2) := by linarith
  -- We discuss the sign of $(a+2)$ and $(a-2)$ to solve the inequality.
  -- If $a-2=0$ therefore $a=2$, then it is trivial that all real numbers satisfy the inequality.
  by_cases hyp₁ : a = 2
  right; right; left; rw [hyp₁] at this; simp only [sub_self, mul_zero, zero_mul, Nat.ofNat_pos,
    mul_pos_iff_of_pos_left, pos_add_self_iff] at this; tauto
  -- if $a+2=0$ therefore $a=-2$, then it is trivial that no real numbers satisfy the inequality.
  by_cases hyp₂ : a = - 2
  right; right; right; rw [hyp₂] at this
  have : 0 < 0 := by linarith
  tauto
  -- if $a+2<0$ therefore $a<-2$, then $a-2<0$ and the desired result follows.
  by_cases hyp₃ : a < - 2
  have : a + 2 < 0 := by linarith
  have p : a - 2 < 0 := by linarith
  have : (a - 2) * x > 3 := by nlinarith
  have : x < 3 / (a - 2) := (lt_div_iff_of_neg' p).mpr this
  left; tauto
  -- if $a-2>0$ therefore $a>2$, then $a+2>0$ and the desired result follows.
  by_cases hyp₄ : a > 2
  have : a + 2 > 0 := by linarith
  have p : a - 2 > 0 := by linarith
  have : (a - 2) * x < 3 := by nlinarith
  have : x < 3 / (a - 2) := (lt_div_iff' p).mpr this
  left; tauto
  -- if $-2 < a< 2$ therefore $a+2>0$ and $a-2<0$, and the desired result follows.
  simp only [not_lt] at hyp₃ hyp₄
  have : a > - 2 := lt_of_le_of_ne hyp₃ fun a_1 => hyp₂ (id (Eq.symm a_1))
  have : a < 2 := lt_of_le_of_ne hyp₄ hyp₁
  have : a + 2 > 0 := by linarith
  have p : a - 2 < 0 := by linarith
  have : (a - 2) * x < 3 := by nlinarith
  have : x > 3 / (a - 2) := (div_lt_iff_of_neg' p).mpr this
  right; left; tauto
  -- now we check that these solutions are valid.
  intro h
  rcases h with ⟨_, _ | _⟩ | ⟨_, _, _⟩  | h₃ | ⟨h₄, _⟩
  -- if $a>2$ then $a+2>0$ and $a-2>0$, we can multiply the inequalities to get the desired result.
  have : a - 2 > 0 := by linarith
  have : a + 2 > 0 := by linarith
  have ineq : (a - 2) * x < 3 / (a - 2) * (a - 2) := by nlinarith
  have : 3 / (a - 2) * (a - 2) = 3 := by rw [div_mul_cancel₀]; linarith
  rw [this] at ineq
  have : (a + 2) * (a - 2) * x < (a + 2) * 3 := by nlinarith
  linarith
  -- if $a<-2$ then $a+2<0$ and $a-2<0$, we can multiply the inequalities to get the desired result.
  have : a - 2 < 0 := by linarith
  have : a + 2 < 0 := by linarith
  have ineq : (a - 2) * x > 3 / (a - 2) * (a - 2) := by nlinarith
  have : 3 / (a - 2) * (a - 2) = 3 := by rw [div_mul_cancel₀]; linarith
  rw [this] at ineq
  have : (a + 2) * (a - 2) * x < (a + 2) * 3 := by nlinarith
  linarith
  -- if $-2 < a< 2$ then $a+2>0$ and $a-2<0$, we can multiply the inequalities to get the desired result.
  have : a - 2 < 0 := by linarith
  have : a + 2 > 0 := by linarith
  have ineq : (a - 2) * x < 3 / (a - 2) * (a - 2) := by nlinarith
  have : 3 / (a - 2) * (a - 2) = 3 := by rw [div_mul_cancel₀]; linarith
  rw [this] at ineq
  have : (a + 2) * (a - 2) * x < (a + 2) * 3 := by nlinarith
  linarith
  -- if $a=2$ plug in and the inequality is trivial.
  simp only [true_and] at h₃
  rw [h₃]; linarith
  -- if $a=-2$ no real numbers satisfy the inequality and the case is trivial.
  exfalso; exact h₄
