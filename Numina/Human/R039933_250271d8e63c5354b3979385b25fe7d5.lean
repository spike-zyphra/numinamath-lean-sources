import Mathlib

/-Suppose that $a^2$ varies inversely with $b^3$. If $a=7$ when $b=3$, find the value of $a^2$ when $b=6$.

The final answer is $ \boxed{6.125} $-/
theorem algebra_10265 {a b : ℝ} (hb : b = 6) :
  let var_inv_k (a b k : ℝ) : Prop := a * b = k;
  var_inv_k (a^2) (b^3) (7^2 * 3^3) → a^2 = 6.125 := by
    intro var_inv_k h1
    -- Since $a^2$ varies inversely with $b^3$, $(a^2)(b^3)=k$ for some constant $k$. If $a=7$ when $b=3$, then $k=(7^2)(3^3)=(49)(27)=1323$. So if $b=6$, \begin{align*} (a^2)(6^3)&=1323
    -- \\ 216a^2&=1323
    -- \\\Rightarrow\qquad a^2&=\boxed{6.125}
    -- \end{align*}
    simp [var_inv_k, hb] at h1
    ring_nf at h1
    apply_fun (· / 216) at h1
    ring_nf at h1
    simp [h1]
    ring_nf
