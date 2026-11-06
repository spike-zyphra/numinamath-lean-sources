import Mathlib

/- 14. Given that $f(x)$ and $g(x)$ are two functions defined on $\mathbf{R}$, and $g(x)$ is an odd function, satisfying $f(0)=1$; for any $x, y \in \mathbf{R}$, we have $f(x-y)=f(x) f(y)+g(x) g(y)$. Prove: (1) For any $x \in \mathbf{R}$, $f^{2}(x)+g^{2}(x)=1$; (2) $f(x)$ is an even function; (3) If there exists a non-zero real number $a$ such that $f(a)=1$, then $f(x)$ is a periodic function. -/
theorem algebra_168533 {f g : ℝ → ℝ} (h_odd : Function.Odd g) (hf0 : f 0 = 1)
    (hf : ∀ x y, f (x - y) = f x * f y + g x * g y) :
    (∀ x, (f x)^2 + (g x)^2 = 1) ∧ Function.Even f ∧
    ((∃ a ≠ 0, f a = 1) → ∃ c, Function.Periodic f c) := by
  have h_sq : ∀ x, (f x)^2 + (g x)^2 = 1
  -- use y = x
  · intro x
    specialize hf x x
    rw [sub_self, hf0] at hf
    rw [pow_two, pow_two]
    exact hf.symm
  -- use y = 2 * x and x = 2 * y
  have h_even : Function.Even f
  · intro x
    have h1 := hf x (2 * x)
    have h2 := hf (2 * x) x
    ring_nf at h1 h2
    rw [h1, ←h2]
  refine ⟨h_sq, h_even, ?_⟩
  intro ⟨a, h_ne, ha⟩
  use a
  intro x
  -- use y = -a and even property proven above
  have := hf x (-a)
  rw [h_odd a, h_even a, sub_neg_eq_add] at this
  rw [this, ha]
  -- show g a = 0 from the first equation
  specialize h_sq a
  rw [ha] at h_sq
  simp at h_sq
  -- conclude
  rw [h_sq]
  simp only [neg_zero, mul_zero, add_zero, mul_one]