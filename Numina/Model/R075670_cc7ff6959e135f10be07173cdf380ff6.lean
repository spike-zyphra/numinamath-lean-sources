import Mathlib

theorem algebra_144571 {x : ℝ} (hx : x > 0) (h : √x / (1 / 2) = x - 3) :
    x = 9 := by
  -- Note that dividing by 1/2 is equivalent to multiplying by 2
  have h1 : √x / (1 / 2) = 2 * √x := by
    field_simp
    <;> ring
  rw [h1] at h
  -- Square both sides to remove the square root
  have h2 : (2 * √x) ^ 2 = (x - 3) ^ 2 := by
    rw [h]
  -- Computes left side
  have h3 : (2 * √x) ^ 2 = 4 * x := by
    calc
      (2 * √x) ^ 2 = 4 * (√x ^ 2) := by ring
      _ = 4 * x := by rw [Real.sq_sqrt (by linarith)]
  -- Expanding right side
  have h4 : (x - 3 : ℝ) ^ 2 = x ^ 2 - 6 * x + 9 := by
    ring
  -- Substitute both sides
  rw [h3] at h2
  rw [h4] at h2
  -- Rearrange to standard form
  have h5 : x ^ 2 - 10 * x + 9 = 0 := by
    nlinarith
  -- Factor the quadratic
  have h6 : (x - 1) * (x - 9) = 0 := by
    nlinarith
  -- Use zero product
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- First case: x - 1 = 0, so x = 1, which does not satisfy original equation
    have hx1 : x = 1 := by linarith
    rw [hx1] at h
    -- Check original equation for x = 1. √1 = 1, so left side is 2, right side is -2: contradiction
    have h10 : √(1 : ℝ) = (1 : ℝ) := Real.sqrt_one
    rw [h10] at h
    nlinarith
  · -- Second case: x - 9 = 0, so x = 9, which is our solution
    linarith