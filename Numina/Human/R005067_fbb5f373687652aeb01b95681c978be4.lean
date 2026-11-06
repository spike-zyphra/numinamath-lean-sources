import Mathlib

/- Let $a, b$, and $c$ be rational numbers for which $a+b c, b+a c$, and $a+b$ are all non-zero and for which it holds that

$$
\frac{1}{a+b c}+\frac{1}{b+a c}=\frac{1}{a+b}
$$

Prove that $\sqrt{(c-3)(c+1)}$ is rational.-/
theorem algebra_605363 {a b c : ℚ} (h1 : a + b * c ≠ 0) (h2 : b + a * c ≠ 0)
    (h3 : a + b ≠ 0) (h : 1 / (a + b * c) + 1 / (b + a * c) = 1 / (a + b)) :
    ∃ q : ℚ, Real.sqrt ((c - 3) * (c + 1)) = q := by

  -- We first show that $(a+b)^{2} = a b(c-1)^{2}$
  have claim1 : (a + b) ^ 2 = a * b * (c - 1) ^ 2 := by
    -- It holds that
    -- $$
    -- \frac{1}{a+b c}+\frac{1}{b+a c}=\frac{(b+a c)+(a+b c)}{(a+b c)(b+a c)}=\frac{(a+b)+(a+b) c}{a b+a^{2} c+b^{2} c+a b c^{2}}
    -- $$
    -- From the given equality, it follows that
    -- $$
    -- (a+b)((a+b)+(a+b) c)=a b+a^{2} c+b^{2} c+a b c^{2}.
    -- $$
    -- Hence $(a+b)^{2} & = a b+a^{2} c+b^{2} c+a b c^{2}-(a+b)^{2} c =a b+a b c^{2}-2 a b c = a b(c-1)^{2}$.
    have h' := calc
      1 / (a + b) =  1 / (a + b * c) + 1 / (b + a * c) := Eq.symm h
      _ = ((b + a * c) + (a + b * c)) / ((a + b * c) * (b + a * c)) := by
        field_simp
      _ = ((a + b) + (a + b) * c) / ((a + b * c) * (b + a * c)) := by
        simp (disch := field_simp_discharge) only [eq_div_iff, div_mul_cancel₀]
        ring
      _ = ((a + b) + (a + b) * c) / (a * b + a ^ 2 * c + b ^ 2 * c + a * b * c ^ 2) := by
        congr
        ring
    have : 1 = ((a + b) ^ 2 + (a + b) ^ 2 * c) / (a * b + a ^ 2 * c + b ^ 2 * c + a * b * c ^ 2) :=
      calc
      _ = (a + b) * 1 / (a + b) := by
        exact Eq.symm (mul_div_cancel_left₀ 1 h3)
      _ = (a + b) * (a + b + (a + b) * c) / (a * b + a ^ 2 * c + b ^ 2 * c + a * b * c ^ 2) := by
        rw [mul_div_assoc, h']
        field_simp
      _ = _ := by
        have : (a + b) * (a + b + (a + b) * c) = ((a + b) ^ 2 + (a + b) ^ 2 * c) := by
          rw [mul_add, ← mul_assoc, pow_two]
        rw [this]
    have h'' : a * b + a ^ 2 * c + b ^ 2 * c + a * b * c ^ 2 ≠ 0 := by
      by_contra hc
      rw [hc] at this
      simp at this
    replace := Eq.symm this
    rw [div_eq_one_iff_eq h''] at this
    calc
      _ = (a + b) ^ 2 + (a + b) ^ 2 * c - (a + b) ^ 2 * c := by
        simp
      _ = a * b + a ^ 2 * c + b ^ 2 * c + a * b * c ^ 2 - (a + b) ^ 2 * c := by
        rw [this]
      _ = _ := by
        linarith

  -- If $c=1$ then the original equation becomes $ \frac{1}{a+b}+\frac{1}{a+b}=\frac{1}{a+b}$ which cannot be true. Therefore, $(c-1) \neq 0$.
  have hc : c - 1 ≠ 0 := by
    by_contra hc
    simp only [(show c = 1 by linarith), mul_one, one_div, add_right_eq_self, inv_eq_zero, add_comm] at h
    exact false_of_ne <| Eq.trans_ne (Eq.symm h) h3

  -- Similarly $a \neq 0$, $b \neq 0$. If $a=0$, the original equation becomes
  -- $$
  -- \frac{1}{b c}+\frac{1}{b}=\frac{1}{b}
  -- $$
  -- which cannot be true. Therefore, $a \neq 0$ and similarly, we see that $b \neq 0$.
  have ha : a ≠ 0 := by
    by_contra hc
    simp_rw [hc, zero_add, one_div, mul_inv_rev, zero_mul, add_zero, add_left_eq_self,
      mul_eq_zero, inv_eq_zero] at h
    obtain h | h := h
    all_goals
    · rw [h, hc] at h1
      simp at h1
  have hb : b ≠ 0 := by
    by_contra hc
    simp_rw [hc, zero_mul, add_zero, one_div, zero_add, mul_inv_rev, add_right_eq_self,
      mul_eq_zero, inv_eq_zero] at h
    obtain h | h := h
    all_goals
    · rw [h, hc] at h2
      simp at h2

  -- We calculate that
  -- $$
  -- \begin{aligned}
  -- (a-b)^{2} & =(a+b)^{2}-4 a b \\
  -- & =a b+a b c^{2}-2 a b c-4 a b \\
  -- & =a b c^{2}-2 a b c-3 a b \\
  -- & =a b(c-3)(c+1).
  -- \end{aligned}
  -- $$
  have claim2 : (a - b) ^ 2 = a * b * (c - 3) * (c + 1) := calc
    (a - b) ^ 2 = (a + b) ^2 - 4 * a * b := by
      ring
    _ = a * b * (c - 1) ^ 2 - 4 * a * b := by
      rw [claim1]
    _ = a * b * (c ^ 2 - 2 * c - 3) := by
      ring
    _ = _ := by
      ring_nf

  -- Combining claim 1 and claim 2, $(c - 3)(c + 1) = (a - b)^2 (c - 1)^2 / (a + b)^2$.
  -- In particular, $(c - 3)(c + 1)$ is the square of a rational number.
  have claim3 : (c - 3) * (c + 1) =  (a - b) ^ 2 * (c - 1) ^ 2 / (a + b) ^ 2 := by
    suffices h : (c - 3) * (c + 1) * (a * b) = (a - b) ^ 2 * (c - 1) ^ 2 / (a + b) ^ 2 * (a * b) by
      exact mul_right_cancel₀ (show (a * b) ≠ 0 by positivity) h
    rw [claim2, claim1]
    simp (disch := field_simp_discharge) only [div_mul_eq_mul_div, eq_div_iff]
    linarith

  let q := (a - b) * (c - 1) / (a + b)
  have hq : 0 ≤ |q| := abs_nonneg q
  use |q|
  
  have : 0 ≤ (c - 3) * (c + 1) := by
    rw [claim3]
    positivity
  rify at claim3  
  rw [Real.sqrt_eq_iff_eq_sq]
  · simp [q, claim3, div_pow, eq_div_iff, div_mul_cancel₀, mul_pow]
  · norm_cast
  · norm_cast
