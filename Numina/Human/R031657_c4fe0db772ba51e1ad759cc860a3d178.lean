import Mathlib

/- 11. Solve the system of equations:


$$

\left\{\begin{array}{l}
a^{2}+3 a+1=(b+c) / 2 \\
b^{2}+3 b+1=(a+c) / 2 \\
c^{2}+3 c+1=(a+b) / 2
\end{array}\right.

$$
 -/
theorem algebra_215731 {a b c : ℝ} (ha : a^2 + 3 * a + 1 = (b + c) / 2)
    (hb : b^2 + 3 * b + 1 = (a + c) / 2) (hc : c^2 + 3 * c + 1 = (a + b) / 2) :
    a = -1 ∧ b = -1 ∧ c = -1 := by
      -- Adding together all equations we get (a + 1) ^ 2 + (b + 1) ^ 2 + (c + 1) ^ 2 = 0
      have added : (a + 1) ^ 2 + (b + 1) ^ 2 + (c + 1) ^ 2 = 0 := by linarith

      -- each term is nonnegative
      have : 0 ≤ (a + 1) ^ 2 := by positivity
      have : 0 ≤ (b + 1) ^ 2 := by positivity
      have : 0 ≤ (c + 1) ^ 2 := by positivity

      -- if sums of nonnegative terms equals zero, then each term equals zero
      have a_eq : (a + 1) ^ 2 = 0 := by linarith
      have b_eq : (b + 1) ^ 2 = 0 := by linarith
      have c_eq : (c + 1) ^ 2 = 0 := by linarith

      -- if x ^ 2 = 0, then x = 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at a_eq b_eq c_eq

      -- if x - 1 = 0 then x = -1, so a = b = c = -1
      refine ⟨?_, ?_, ?_⟩
      linarith only [a_eq]
      linarith only [b_eq]
      linarith only [c_eq]