import Mathlib

open Real
open scoped BigOperators

-- Cauchy-Schwarz inequality
lemma CSineq  (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) : (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) ^ 2 ≤
    (a₁ * a₁ + a₂ * a₂ + a₃ * a₃) * (b₁ * b₁ + b₂ * b₂ + b₃ * b₃) := by
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁), sq_nonneg (a₂ * b₃ - a₃ * b₂),
    sq_nonneg (a₃ * b₁ - a₁ * b₃)]

-- Cauchy-Schwarz inequality with equality condition
lemma CSineq' (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) (h : (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) ^ 2 =
    (a₁ * a₁ + a₂ * a₂ + a₃ * a₃) * (b₁ * b₁ + b₂ * b₂ + b₃ * b₃)) :
    a₁ * b₂ = a₂ * b₁ ∧ a₁ * b₃ = a₃ * b₁ := by
  constructor
  · nlinarith [sq_nonneg (a₁ * b₃ - a₃ * b₁), sq_nonneg (a₂ * b₃ - a₃ * b₂)]
  · nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁), sq_nonneg (a₂ * b₃ - a₃ * b₂)]

lemma pow_sqrt_comm {x : ℝ} (xpos : x ≥ 0) : √(x ^ 3) = √x ^ 3 := by
  refine (sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr ?_
  rw [← mul_pow, ← pow_two, Real.sq_sqrt (by positivity)]

-- A rewriting lemma for the main theorem
lemma lemma_2(x y z : ℝ) (xpos : x ≥ 0) (ypos : y ≥ 0) (zpos : z ≥ 0) :
    (√(x * y ^ 3) * √z + √(y * z ^ 3) * √x + √(z * x ^ 3) * √y) *
    (√(x * y ^ 3) * √z + √(y * z ^ 3) * √x + √(z * x ^ 3) * √y) = x * y * z * (x + y + z) ^ 2 := by
    simp [Real.sqrt_mul xpos, Real.sqrt_mul ypos, Real.sqrt_mul zpos]
    nth_rw 7 [← Real.sq_sqrt xpos, ← Real.sq_sqrt ypos, ← Real.sq_sqrt zpos]
    nth_rw 8 [← Real.sq_sqrt xpos, ← Real.sq_sqrt ypos, ← Real.sq_sqrt zpos]
    rw [pow_sqrt_comm xpos, pow_sqrt_comm ypos, pow_sqrt_comm zpos]
    ring

lemma eq_1 {x y z : ℝ} (xpos : x ≥ 0) (ypos : y ≥ 0) (zpos : z ≥ 0) :
    (√(x * y ^ 3) * √z + √(y * z ^ 3) * √x + √(z * x ^ 3) * √y) ^ 2 =
    x * y * z * (y + z + x) ^ 2 := by
  have h1 : √(x * y ^ 3) * √z = √(x * y * z) * y := by
    nth_rw 3 [← Real.sqrt_mul_self ypos]
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have h2 : √(y * z ^ 3) * √x = √(x * y * z) * z := by
    nth_rw 3 [← Real.sqrt_mul_self zpos]
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have h3 : √(z * x ^ 3) * √y = √(x * y * z) * x := by
    nth_rw 3 [← Real.sqrt_mul_self xpos]
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  simp [h1, h2, h3, ← mul_add, mul_pow]
  rw [Real.sq_sqrt (by positivity)]
  left
  rfl

lemma eq2 {x y z : ℝ} (xpos : x ≥ 0) (ypos : y ≥ 0) (zpos : z ≥ 0) :
    (√(x * y ^ 3) * √(x * y ^ 3) + √(y * z ^ 3) * √(y * z ^ 3) + √(z * x ^ 3) * √(z * x ^ 3)) *
    (√z * √z + √x * √x + √y * √y) = (x * y ^ 3 + y * z ^ 3 + z * x ^ 3) * (z + x + y) := by
  simp [← pow_two, Real.sq_sqrt xpos, Real.sq_sqrt ypos, Real.sq_sqrt zpos]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  left
  ring

-- First direction of the main theorem
lemma lemma_1 (x y z : ℝ) (xpos : x ≥ 0) (ypos : y ≥ 0) (zpos : z ≥ 0) :
  (x * y^3 + y * z^3 + z * x^3) * (x + y + z) ≥ x * y * z * (x + y + z)^2 := by
  have H := CSineq √(x * y^3) √(y * z^3) √(z * x^3) √z √x √y
  rw [eq_1 xpos ypos zpos, eq2 xpos ypos zpos] at H
  linarith

-- A helper lemma for the main theorem
lemma lemma_3 (x y z : ℝ) (xpos : x > 0) (ypos : y > 0) (zpos : z > 0) (h1 : x^2 * y^2 = z^4)
  (h2 : y^4 = z^2 * x^2) : y + z = z + x ∧ z + x = y + x := by
  have h1 : z^2 = x*y := by
    apply_fun (fun x => √ x ) at h1
    field_simp at h1
    rw [show z^4 = z^2 * z^2 by linarith, Real.sqrt_mul_self] at h1
    linarith
    apply pow_nonneg
    linarith
  rw [h1] at h2
  have : y ^ 3 = x ^ 3 := by
    nlinarith [h2, ypos]
  have : x = y := by
    have h1 : y ^ 3 - x ^ 3 = 0 := by linarith
    have h2 : (y - x) * (y ^ 2 + y * x + x ^ 2) = 0 := by
      ring_nf at h1 ⊢
      exact h1
    cases' (mul_eq_zero.mp h2) with h3 h4
    · linarith
    · have h5 : (y + x / 2) ^ 2 + (3 / 4) * x ^ 2 = 0 := by
        nlinarith
      have h7 : (y + x / 2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (y + x / 2), mul_nonneg (by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ)) (sq_nonneg x)]
      have h8 : y + x / 2 = 0 := by
        rw [sq_eq_zero_iff] at h7
        exact h7
      have h9 : (3 / 4) * x ^ 2 = 0 := by
        linarith [h5, h7]
      have h10 : x ^ 2 = 0 := by
        nlinarith
      have hx : x = 0 := by
        rw [sq_eq_zero_iff] at h10
        exact h10
      have hy : y = 0 := by
        rw [hx] at h8
        linarith
      linarith [hx, hy]
  subst this
  have : z = x := by
    nlinarith
  subst this
  tauto

/- 9. (USA 3) ${ }^{\mathrm{IMO} 6}$ If $a, b$, and $c$ are sides of a triangle, prove that  $$ a^{2} b(a-b)+b^{2} c(b-c)+c^{2} a(c-a) \geq 0 $$  Determine when there is equality. -/
theorem  other_23904 {a b c : ℝ} (apos : a > 0) (bpos : b > 0) (cpos : c > 0)
    (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
    a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 ∧
    (a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) = 0 ↔
    (a = b ∧ b = c)) := by
  -- The basic idea is to use the Cauchy-Schwarz inequality
  have ⟨x, y, z, xpos', ypos', zpos', aeq, beq, ceq, sumpos⟩ :
      ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧
        a = y + z ∧ b = z + x ∧ c = x + y ∧ x + y + z > 0 := by
      /-
        we set
        $$
        \begin{aligned}
        x &= \frac{-a + b + c}{2} \\
        y &= \frac{a - b + c}{2} \\
        z &= \frac{a + b - c}{2}
        \end{aligned}
        $$
      -/
      use (- a + b + c) / 2,
          (a - b + c) / 2,
          (a + b - c) / 2
      repeat constructor; try nlinarith
      nlinarith
  have : -(y * z * x^2 * 2) - y * z^2 * x * 2 + (y * z^3 * 2 - y^2 * z * x * 2) + y^3 * x * 2 + z * x^3 * 2 =
      -(y * z * x^2 * 2 + y * z^2 * x * 2 + y^2 * z * x * 2) + (y * z^3 * 2 + y^3 * x * 2 + z * x^3 * 2) := by
    ring
  rw [aeq, beq, ceq]
  ring_nf
  rw [this]
  constructor
  . -- Use the Cauchy-Schwarz inequality
    have : x * y^3 + y * z^3 + z * x^3 ≥ x * y * z * (x + y + z) := by
      simp
      rw [← mul_le_mul_right (a := x + y + z) sumpos]
      linarith [lemma_1 x y z (by linarith) (by linarith) (by linarith)]
    linarith
  constructor
  . intro h
    have h : (x * y^3 + y * z^3 + z * x^3) * (x + y + z) = x * y * z * (x + y + z)^2 := by nlinarith
    have := CSineq' √(x * y^3) √(y * z^3) √(z * x^3) √z √x √y ?_
    . rcases this with ⟨h1, h2⟩
      apply_fun (fun x => x ^ 2) at h1 h2
      rw [← sqrt_mul (by positivity), ← sqrt_mul (by positivity),
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h1 h2
      ring_nf at h1 h2
      apply lemma_3 x y z xpos' ypos' zpos'
      · rw [← mul_right_inj' (a := y) (by positivity), ← h1]
        ring
      · rw [← mul_right_inj' (a := x) (by positivity), h2]
        ring
    . rw [eq_1 (by linarith) (by linarith) (by linarith),
        eq2 (by linarith) (by linarith) (by linarith)]
      linarith
  . intro ⟨h1, h2⟩
    simp [add_comm] at h1 h2
    rw [h2, h1]
    linarith