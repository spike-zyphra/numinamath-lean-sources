import Mathlib
/-Given the polynomial $f(x) = 5x^5 + 4x^4 + 3x^3 + 2x^2 + x$, calculate the value of this polynomial at $x=3$ using the Horner's method (calculation process required).-/

theorem algebra_9276 {f : Polynomial ℤ} {X : ℤ} (hf : f = 5 * X ^ 5 + 4 * X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + X) (h : X = 3) : f = 1641 := by
  have w : f = ((((5 * X + 4) * X + 3) * X + 2) * X + 1) * X := by
    simp [hf]
    ring
  --The polynomial $f(x) = 5x^5 + 4x^4 + 3x^3 + 2x^2 + x$ can be rewritten using Horner's method as:
  --$$f(x) = ((((5x + 4)x + 3)x + 2)x + 1)x$$
  --Let's calculate it step by step:
  have v1 : 5 * X + 4 = 19 := by
    rw[h]
    norm_num
  --- $v_1 = 5 \times 3 + 4 = 19$
  have v2 : 19 * X + 3 = 60 := by
    rw[h]
    norm_num
  --- $v_2 = 19 \times 3 + 3 = 60$
  have v3 : 60 * X + 2 = 182 := by
    rw[h]
    norm_num
  --- $v_3 = 60 \times 3 + 2 = 182$
  have v4 : 182 * X + 1 = 547 := by
    rw[h]
    norm_num
  --- $v_4 = 182 \times 3 + 1 = 547$
  have v5 : 547 * X = 1641 := by
    rw[h]
    norm_num
  --- $v_5 = 547 \times 3 + 0 = 1641$
  rw[h] at hf
  simp[hf]
  norm_num
  --Therefore, when $x=3$, $f(x) = 1641$.
  