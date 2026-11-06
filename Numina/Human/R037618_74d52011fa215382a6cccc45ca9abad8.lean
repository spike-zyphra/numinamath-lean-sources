import Mathlib

open Real Set
open scoped BigOperators

/- Let $\mathbb{R}$ be the set of real numbers. Let $f: \mathbb{R} \rightarrow \mathbb{R}$ be a function such that  $$ f(x+y) f(x-y) \geqslant f(x)^{2}-f(y)^{2} $$  for every $x, y \in \mathbb{R}$. Assume that the inequality is strict for some $x_{0}, y_{0} \in \mathbb{R}$. Prove that $f(x) \geqslant 0$ for every $x \in \mathbb{R}$ or $f(x) \leqslant 0$ for every $x \in \mathbb{R}$. (Malaysia) -/
theorem inequalities_607735 {f : ℝ → ℝ}
  (h : ∀ x y, f (x + y) * f (x - y) ≥ f x ^ 2 - f y ^ 2)
  (h' : ∃ x₀ y₀, f (x₀ + y₀) * f (x₀ - y₀) > f x₀ ^ 2 - f y₀ ^ 2) :
    (∀ x, f x ≥ 0) ∨ (∀ x, f x ≤ 0) := by
  have crux : ∀ s t, f s * (f t + f (-t)) ≥ 0 := by
    intro s t
    -- We introduce the new variables $s:=x+y$ and $t:=x-y$.
    -- Equivalently, $x=\frac{s+t}{2}$ and $y=\frac{s-t}{2}$. 
    have := h ((s + t) / 2) ((s - t) / 2)
    have h1 : f s * f t ≥ f ((s + t) / 2) ^ 2 - f ((s - t) / 2) ^ 2 := by 
      linear_combination (norm := ring_nf) this
      rfl
    -- The inequality becomes $$ f(s) f(t) \geqslant f\left(\frac{s+t}{2}\right)^{2}-f\left(\frac{s-t}{2}\right)^{2} $$ for every $s, t \in \mathbb{R}$. 
    -- We replace $t$ by $-t$ to obtain $$ f(s) f(-t) \geqslant f\left(\frac{s-t}{2}\right)^{2}-f\left(\frac{s+t}{2}\right)^{2} $$ 
    have := h ((s - t) / 2) ((s + t) / 2)
    have h2 : f s * f (-t) ≥ f ((s - t) / 2) ^ 2 - f ((s + t) / 2) ^ 2 := by
      linear_combination (norm := ring_nf) this
      rfl
    -- Summing the previous two inequalities gives $$ f(s)(f(t)+f(-t)) \geqslant 0 $$ for every $s, t \in \mathbb{R}$. 
    linear_combination (norm := ring_nf) h1 + h2
    rfl
  obtain ⟨x₀, y₀, hxy₀⟩ := h'
  -- This inequality is strict for $s=x\_{0}+y\_{0}$ and $t=x\_{0}-y\_{0}$ by assumption.
  have : f (x₀ + y₀) * (f (x₀ - y₀) + f (-(x₀ - y₀))) > 0 := by
    let s := x₀ + y₀
    let t := x₀ - y₀
    have h2 := h ((s - t) / 2) ((s + t) / 2)
    linear_combination (norm := ring_nf) h2 + hxy₀
    rfl
  -- In particular, there exists some $t\_{0}=x\_{0}-y\_{0}$ for which $f\left(t\_{0}\right)+f\left(-t\_{0}\right) \neq 0$. 
  let t₀ := x₀ - y₀
  have : f t₀ + f (-t₀) ≠ 0 := by
    intro H
    simp only [neg_sub, t₀] at H
    simp [H] at this
  -- Since $f(s)\left(f\left(t\_{0}\right)+\right.$ $\left.f\left(-t\_{0}\right)\right) \geqslant 0$ for every $s \in \mathbb{R}$, we conclude that $f(s)$ must have constant sign.
  cases (lt_or_gt_of_ne (id (Ne.symm this))) with
  | inl hl => 
    left
    intro s
    specialize crux s t₀
    nlinarith
  | inr hr => 
    right
    intro s
    specialize crux s t₀
    nlinarith