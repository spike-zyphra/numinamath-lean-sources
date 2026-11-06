import Mathlib

/- Let x, y and z be positive real numbers that satisfy the following system of equations:
log_2(x/(yz)) = 1/2
log_2(y/(xz)) = 1/3
log_2(z/(xy)) = 1/4
Then the value of |log_2(x^4 y^3 z^2)| is m/n where m and n are relatively prime \
positive integers. Find m+n. -/

theorem algebra_93287 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
(h1 : Real.logb 2 (x / (y * z)) = 1 / 2) (h2 : Real.logb 2 (y / (x * z)) = 1 / 3)
(h3 : Real.logb 2 (z / (x * y)) = 1 / 4) :
∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m.Coprime n ∧ |Real.logb 2 (x ^ 4 * y ^ 3 * z ^ 2)| = m / n := by
  -- denote log_2(x) as a, log_2(y) as b, log_2(z) as c
  have :∃a, a=Real.logb 2 x := by simp
  obtain ⟨a, ha⟩ := this
  have :∃b, b=Real.logb 2 y := by simp
  obtain ⟨b, hb⟩ := this
  have :∃c, c=Real.logb 2 z := by simp
  obtain ⟨c, hc⟩ := this
  -- with this, we can convert h1, h2, h3 into system of linear equations
  have h1' : 1/2 = a - b - c := by
    calc 1/2
    _ = Real.logb 2 (x / (y * z)) := by rw [← h1]
    _ = Real.logb 2 x - (Real.logb 2 y + Real.logb 2 z) := by rw [Real.logb_div (by linarith) (by simp; exact ⟨by linarith, by linarith⟩), Real.logb_mul (by linarith) (by linarith)]
    _ = a - b - c := by rw [ha, hb, hc]; ring_nf
  have h2' : 1/3 = b - a - c := by
    calc 1/3
    _ = Real.logb 2 (y / (x * z)) := by rw [← h2]
    _ = Real.logb 2 y - (Real.logb 2 x + Real.logb 2 z) := by rw [Real.logb_div (by linarith) (by simp; exact ⟨by linarith, by linarith⟩), Real.logb_mul (by linarith) (by linarith)]
    _ = b - a - c := by rw [ha, hb, hc]; ring_nf
  have h3' : 1/4 = c - a - b := by
    calc 1/4
    _ = Real.logb 2 (z / (x * y)) := by rw [← h3]
    _ = Real.logb 2 z - (Real.logb 2 x + Real.logb 2 y) := by rw [Real.logb_div (by linarith) (by simp; exact ⟨by linarith, by linarith⟩), Real.logb_mul (by linarith) (by linarith)]
    _ = c - a - b := by rw [ha, hb, hc]; ring_nf

  -- we solve the system and obtain a=-7/24, b=-9/24, c=-5/12
  have h: a=-7/24 ∧ b=-9/24 ∧ c=-5/12 := by exact ⟨ by linarith, ⟨ by linarith, by linarith ⟩ ⟩
  -- we calculate the log in the question
  have h2:=
    calc 4*a + 3*b + 2*c
    _ = (4:ℕ)*(Real.logb 2 x) + (3:ℕ)*(Real.logb 2 y) + (2:ℕ)*(Real.logb 2 z) := by rw [ha, hb, hc]; ring_nf
    _ = Real.logb 2 (x^4) + Real.logb 2 (y^3) + Real.logb 2 (z^2) := by rw [← Real.logb_pow, ← Real.logb_pow, ← Real.logb_pow]
    _ = Real.logb 2 (x^4 * y^3 * z^2) := by rw [Real.logb_mul (by simp; exact ⟨by linarith, by linarith⟩) (by simp; linarith), Real.logb_mul (by simp; linarith) (by simp; linarith)]
  rw [← h2, h.left, h.right.left, h.right.right]
  -- now we just need to show the fraction is correct
  norm_num
  use 25, (by norm_num), 8, (by norm_num)
  norm_num