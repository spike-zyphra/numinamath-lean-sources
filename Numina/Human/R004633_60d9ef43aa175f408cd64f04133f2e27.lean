import Mathlib

/- 1. If positive numbers $a, b$ satisfy $2+\log _{2} a=3+\log _{3} b=\log _{6}(a+b)$, then the value of $\frac{1}{a}+\frac{1}{b}$ is -/
theorem algebra_291614 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 2 + Real.logb 2 a = 3 + Real.logb 3 b) (h' : 3 + Real.logb 3 b = Real.logb 6 (a + b)) :
    1 / a + 1 / b = 108 := by
  let q: (∃ k:ℝ, k = 2 + Real.logb 2 a) := by
    use 2 + Real.logb 2 a
  -- let k be the value of the equalities
  obtain ⟨k, kdef⟩ := q
  -- then we can easily obtain a and b from k
  have h1: a = 2 ^ (k - 2) := by rw [kdef]; simp; rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
  have h2: b = 3 ^ (k - 3) := by rw [h] at kdef; apply congr_arg (fun x=> x-3) at kdef; rw [kdef]; simp; rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
  have h3: a + b = 6 ^ k := by rw [h, h'] at kdef; rw [kdef]; rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
  -- just combine to get the result
  calc 1 / a + 1 / b
  _ = (a + b) / (a * b) := by ring_nf; rw [mul_inv_cancel₀ (by linarith), one_mul, mul_assoc, mul_inv_cancel₀ (by linarith), mul_one, add_comm]
  _ = 6 ^ k / (2 ^ (k - 2) * 3 ^ (k - 3)) := by rw [h3, h1, h2]
  _ = 6 ^ k * 2 ^ (2 - k) * 3 ^ (3 - k) := by field_simp; ring_nf; rw [mul_assoc, mul_assoc, mul_comm, mul_comm (2 ^ (-2 + k)), ← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num), mul_assoc, mul_comm (6^k), ← mul_assoc, mul_assoc (3^_), ← Real.rpow_add (by norm_num)]; ring_nf;
  _ = 6 ^ k * 2 ^ (2 - k) * 3 ^ (2 - k) * 3 ^ (1:ℝ) := by rw [mul_assoc (6 ^ k * 2 ^ (2 - k)), ← Real.rpow_add (by norm_num)]; ring_nf
  _ = 6 ^ k * 6 ^ (2 - k) * 3 := by rw [mul_assoc (6 ^ k), ← Real.mul_rpow (by norm_num) (by norm_num)]; ring_nf
  _ = 6 ^ 2 * 3 := by rw [← Real.rpow_add (by norm_num)]; ring_nf
  _ = 108 := by norm_num