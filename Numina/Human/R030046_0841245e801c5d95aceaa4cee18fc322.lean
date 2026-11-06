import Mathlib

/- Let $a$, $b$, and $c$ be three positive real numbers such that $a(a+b+c)=bc$. Determine the maximum value of $\frac{a}{b+c}$. -/
theorem algebra_9125 :
  IsGreatest {y | ∃ a b c : ℝ,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    a * (a + b + c) = b * c ∧
    y = a / (b + c)}
  ((Real.sqrt 2 - 1) / 2) := by

  constructor
  all_goals simp_all
  pick_goal 2
  intro y hy
  dsimp at hy
  obtain ⟨a, ha, b, hb, c, hc, h, hy'⟩ := hy

  -- Rewrite the equation `a * (a + b + c) = b * c` into a quadratic equation.
  have h₀ : 1 * (a * a) + (b + c) * a + - b * c = 0 := by
    calc
      1 * (a * a) + (b + c) * a + - b * c = a * (a + b + c) - b * c := by ring
      _ = b * c - b * c := by rw [h]
      _ = 0 := by simp

  -- Ensure that the leading coefficient of the quadratic equation is non-zero.
  all_goals have h1n0 : (1:ℝ) ≠ 0 := by linarith

  -- Calculate the discriminant of the quadratic equation.
  generalize ht : discrim 1 (b + c) (- b * c) = t
  have ht₀ : discrim 1 (b + c) (-b * c) = (b + c) ^ 2 - 4 * 1 * (-b * c) := by unfold discrim; rfl
  unfold discrim at ht
  have h0let : 0 ≤ t := by nlinarith

  -- Use the quadratic formula to find the roots of the equation.
  have ht₁ : √t * √t = t := by simp [h0let]
  rw [ht, ← ht₁] at ht₀
  let hroot := quadratic_eq_zero_iff h1n0 ht₀ a
  rw [hroot] at h₀
  simp only [mul_one] at h₀

  -- Case 1: a = (-(b + c) + √t) / 2
  cases h₀
  . rename_i hroot_l
    -- Simplify the inequation.
    simp at ht
    rw [hy', hroot_l, ← ht]
    rw [div_right_comm, div_le_div_right, add_div, neg_div_self]
    simp
    have h0 : 0 ≤ √2 := by norm_num
    have h1 : 0 ≤ √((b + c) ^ 2 + 4 * (b * c)) := by norm_num
    have h0ltbpc : 0 < b + c := by linarith
    let h3 := div_nonneg h1 h0ltbpc.le
    rw [← abs_eq_self] at h0
    rw [← abs_eq_self] at h3
    rw [← h0, ← h3, ← sq_le_sq]
    simp_all; rw [← ht, add_comm]
    nth_rw 2 [← one_add_one_eq_two]; simp
    have : (1:ℝ) = 4 * (1 / 4) := by norm_num
    have : 0 < (b + c) ^ 2 := by nlinarith
    let k := two_mul_le_add_sq b c
    have : 4 * (b * c) ≤ (b + c) ^ 2 := by
      calc
        4 * (b * c) = 2 * b * c + 2 * b * c := by ring
        _ ≤ b ^ 2 + c ^ 2 + 2 * b * c := by linarith
        _ = (b + c) ^ 2 := by ring
    rw [div_pow]
    simp only [ge_iff_le]
    have : 0 ≠ b + c := by linarith
    rw[Real.sq_sqrt, div_le_iff₀]
    all_goals nlinarith


  -- Case 2: a = (-(b + c) - √t) / 2
  . rename_i hroot_r
    have : -√t ≤ 0 := by norm_num
    linarith

  -- When a = (√2 - 1)b, b = c, the function attains its maximum value.
  use √2 - 1
  constructor; swap
  use 1
  constructor; swap
  use 1
  -- Simplify the remaining inequalities and equations, and prove that they hold.
  constructor; swap
  constructor
  all_goals ring_nf
  any_goals simp
  any_goals nlinarith
  rw [← Real.sqrt_one]
  rw [Real.sqrt_lt_sqrt_iff]
  all_goals nlinarith
