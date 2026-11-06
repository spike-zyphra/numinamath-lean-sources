import Mathlib

/-The function $f$ has the property that for each real number $x$ in its domain, $1/x$ is also in its domain and \[
f(x) + f\left(\frac{1}{x}\right) = x.
\]What is the largest set of real numbers that can be in the domain of $f$?

(a) ${\{x\mid x\ne0\}}$

(b) ${\{x\mid x<0\}}$

(c) ${\{x\mid x>0\}}$

(d) ${\{x\mid x\ne-1\ \text{and}\ x\ne0\ \text{and}\ x\ne1\}}$

(e) ${\{-1,1\}}$-/
theorem algebra_13636 {dom: Set ℝ} {f : ℝ → ℝ}
    (hd: ∀x∈dom, 1/x ∈dom) (hf : ∀x∈dom, f x + f (1/x) = x)
    (h : 0 ∉ dom) : (∀x∈dom, x = -1 ∨ x = 1) := by
  intro x hx
  -- for each real number $x$ in its domain, $1/x$ is also in its domain
  have hx' := hd x hx
  -- x = f(x) + f(1/x)
  have hf' := hf x hx
  -- 1/x = f(1/x) + f(x)
  have hp' := hf (1/x) hx'
  field_simp at hp' hf'
  rw [add_comm] at hp'
  -- Simultaneous, and get 1/x = x
  rw [hp'] at hf'

  have : x ≠ 0 := by
    -- x ≠ 0, because 1/0 is undefined. However, in mathlib, 1/0 is defined as 0.
    -- So we need to either manually add the condition, or add an axiom that can derive x ≠ 0 from 1/x, but this is less convenient than directly adding (h : 0 ∉ dom).
    by_contra!
    rw [this] at hx
    exact h hx

  -- to solve the equation x = 1/x.
  have : x * x - 1 = 0 := by
    rw (config := {occs := .pos [2]}) [hf'.symm]
    rw [mul_div, mul_comm, ←mul_div, div_self]
    linarith
    exact this
  have : (x - 1) * (x + 1) = 0 := by linarith
  -- simp can split equation (x - a) * (x - b) * (...) * (x - z) = 0 into x = a ∨ x = b, ...
  simp at this
  rcases this with hl | hr
  apply Or.inr
  linarith
  apply Or.inl
  linarith
