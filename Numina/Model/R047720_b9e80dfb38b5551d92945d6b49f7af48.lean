import Mathlib

theorem algebra_155942 :
    IsLeast {√(a * b) + √(b * c) + √(c * a) | (a : ℝ) (b : ℝ) (c : ℝ) (_ : 0 ≤ a) (_ : 0 ≤ b) (_ : 0 ≤ c) (_ : a * b + b * c + c * a = a + b + c) (_ : a + b + c > 0)} 2 := by
  constructor
  · -- First, show that 2 belongs to the set
    use 0, 2, 2
    simp
    <;> norm_num
  · -- Now, show that 2 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_eq, h0, rfl⟩

    have h1 : √(a * b) = √a * √b := by
      rw [Real.sqrt_mul (by linarith)]

    have h2 : √(b * c) = √b * √c := by 
      rw [Real.sqrt_mul (by linarith)]

    have h3 : √(c * a) = √c * √a := by 
      rw [Real.sqrt_mul (by linarith)]

    rw [h1, h2, h3]

    have h4 : √a ^ 2 = a := by
      rw [Real.sq_sqrt]
      exact ha

    have h5 : √b ^ 2 = b := by
      rw [Real.sq_sqrt]
      exact hb

    have h6 : √c ^ 2 = c := by
      rw [Real.sq_sqrt]
      exact hc

    -- Now we need to use the condition `a * b + b * c + c * a = a + b + c`.
    -- To use it with √a, √b, √c, rewrite it in terms of √a, √b, √c.

    have eq1 : a * b = (√a * √b) ^ 2 := by
      have h4 : √a ^ 2 = a := h4
      have h5 : √b ^ 2 = b := h5
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

    have eq2 : b * c = (√b * √c) ^ 2 := by
      have h5 : √b ^ 2 = b := h5
      have h6 : √c ^ 2 = c := h6
      nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg c]

    have eq3 : c * a = (√c * √a) ^ 2 := by
      have h4 : √a ^ 2 = a := h4
      have h6 : √c ^ 2 = c := h6
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg c]

    -- Now rewrite `h_eq` using eq1, eq2, eq3 to get the condition in terms of √a, √b, √c.
    have h7 : (√a * √b) ^ 2 + (√b * √c) ^ 2 + (√c * √a) ^ 2 = (√a)^2 + (√b)^2 + (√c)^2 := by
      nlinarith [h_eq, eq1, eq2, eq3, h4, h5, h6]

    nlinarith [sq_nonneg (√a - √b), sq_nonneg (√b - √c), sq_nonneg (√c - √a),
      Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
      mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
      h7, h0]