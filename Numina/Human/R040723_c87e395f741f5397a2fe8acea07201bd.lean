import Mathlib

/- Problem 1. (5 points) The functions $f$ and $g$ are such that $g(f(x))=x$ and $f(g(x))=x$ for any real number $x$. If for any real number $x$ the equality $f(x)=k x+h(x)$ holds, where $k$ is a constant and $h(x)$ is a periodic function, prove that $g(x)$ can similarly be represented as the sum of a linear and a periodic function. (A function $h$ is called periodic if for any real number $x$ the equality $h(x+p)=h(x)$ holds, where $p$ is a fixed non-zero real number.) -/
theorem algebra_293849 {f g : ℝ → ℝ} (hfg : ∀ x, g (f x) = x ∧ f (g x) = x)
    (hf : ∃ k : ℝ, ∃ h : ℝ → ℝ, (∀ x, f x = k * x + h x) ∧
      (∃ d : ℝ, d ≠ 0 ∧ ∀ x, h x = h (x + d))) :
    ∃ k : ℝ, ∃ h' : ℝ → ℝ, (∀ y, g y = k * y + h' y) ∧
      (∃ d' : ℝ, d' ≠ 0 ∧ ∀ y, h' y = h' (y + d')) := by
  -- Solution: Let $d \neq 0$ be the period of the function $h$ (i.e., $h(x)=h(x+d)$ for every $x$).
  rcases hf with ⟨k, h, f_x_eq_kx_add_h_x, d, d_nonzero, h_x_eq_h_x_add_d⟩
  have gf_eq x := (hfg x).1
  have fg_eq x := (hfg x).2
  -- Note that $k \neq 0$ (otherwise $f(x)=h(x)$, which implies $f(0)=f(d)$, and thus $0=g(f(0))=g(f(d))=d$, a contradiction).
  have k_nonzero : k ≠ 0 := by
    intro k_eq_0
    simp [k_eq_0] at f_x_eq_kx_add_h_x
    have /- : 0 = d -/ := by
      have := h_x_eq_h_x_add_d 0
      simp at this
      rw [←f_x_eq_kx_add_h_x, ←f_x_eq_kx_add_h_x] at this
      have := congrArg g this
      rw [gf_eq, gf_eq] at this
      exact this
    exact d_nonzero this.symm
  -- It is also clear that the function $f$ takes all real values: by the condition $f(g(y))=y$ for every $y$ (the value $y$ is achieved at the point $g(y)$).
  /- This is actually not needed.
  have Surjective_f : Function.Surjective f := by
    intro x
    use g x
    exact fg_eq x
   -/
  -- Clearly, $g(y)=\frac{y}{k}+\left(g(y)-\frac{y}{k}\right)$. The function $\frac{y}{k}$ is linear, so it is sufficient to prove that the function $s(y)=g(y)-\frac{y}{k}$ is periodic. We will prove that $k d$ is the period of this function.
  let s y := g y - (y / k)
  use 1 / k, s
  constructor
  . intro y
    ring
  . use k * d, by simp [k_nonzero, d_nonzero] --(mul_ne_zero_iff_right d_nonzero).mpr k_nonzero
    /-
    First, $x=g(f(x))$ and

    $x+d=g(f(x+d))=g(k(x+d)+h(x+d))=g(k x+k d+h(x))=g(f(x)+k d)$.
    -/
    have : ∀ x, x + d = g (f x + k * d) := by
      intro x
      conv_lhs =>
        rw [←gf_eq (x + d), f_x_eq_kx_add_h_x]
        --change g (k * x + k * d + h x)
        rw [show k * (x + d) + h (x + d) = k * x + h x + k * d/- k * x + k * d + h x -/ by
          rw [←h_x_eq_h_x_add_d]
          ring
        ]
        rw [←f_x_eq_kx_add_h_x]
    /-
    By denoting $f(x)$ as $y$, we get that $g(y)+d=g(y+k d)$ for every $y$ (since $f(x)$ takes all real values). Then

    $$ s(y+k d)=g(y+k d)-\frac{y+k d}{k}=g(y)+d-\left(\frac{y}{k}+d\right)=g(y)-\frac{y}{k}=s(y) $$
    -/
    --have : ∀ y, s (y + k * d) = s y := by
    intro y
    have : g y + d = g (y + k * d) := by
      have := this (g y)
      rw [fg_eq] at this
      exact this
    symm
    conv_lhs =>
      unfold s
      rw [←this]
      rw [show g y + d - (y + k * d) / k = g y - (y / k) by
        field_simp
        ring
      ]
    -- i.e., $s(y)$ is periodic (with period $k d$), which is what we needed to prove.
