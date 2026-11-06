import Mathlib

theorem algebra_292264 {a b c x y : ℝ} (h₀ : a + b + c = 0) (h₁ : a - 2 = x + y)
    (M : ℝ) (hM : M = ∑ i ∈ Finset.range 50, x ^ i) :
    a ^ 3 + a ^ 2 * c - a * b * c + b ^ 2 * c + b ^ 3 = 0 ∧
    a * x + 2 * x + a * y + 2 * y + 4 = a ^ 2 ∧
    M * x - M = x ^ 50 - 1 := by
  constructor
  · -- Prove that \(a^{3}+a^{2} c-a b c+b^{2} c+b^{3}=0\), if \(a+b+c=0\)
    have h2 : c = -a - b := by linarith
    rw [h2]
    ring
  constructor
  · -- Prove that \(a x+2 x+a y+2 y+4=a^{2}\), if \(a-2=x+y\)
    have h2 : x + y = a - 2 := by linarith
    have eq1 : a * x + 2 * x + a * y + 2 * y + 4 = a * (x + y) + 2 * (x + y) + 4 := by ring
    rw [eq1]
    rw [h2]
    ring
  · -- Prove that \(M x-M=x^{50}-1\), if \(M=1+x+x^{2}+\ldots+x^{49}\)
    rw [hM]
    have eq1 : (∑ i in Finset.range 50, x ^ i) * x - (∑ i in Finset.range 50, x ^ i) = x ^ 50 - 1 := by
      norm_num [Finset.sum_range_succ]
      <;> ring
    simpa using eq1