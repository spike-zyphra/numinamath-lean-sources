import Mathlib

/- # Problem I-1

Let $\mathbb{R}$ be the set of real numbers. Determine all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
f(x+f(x+y))=x+f(f(x)+y)
$$

holds for all $x, y \in \mathbb{R}$.
 -/
theorem algebra_291755 (f : ℝ → ℝ) :
    (∀ x y, f (x + f (x + y)) = x + f (f x + y)) ↔
    ∃ c, ∀ x, f x = x + c := by
  constructor
  . -- Solution. Denote by $P(x, y)$ the given assertion.
    intro p
    -- Taking $y=-f(x)$ we get the equality $f(x+f(x-f(x)))=x+f(0)$, which implies that $f$ is surjective.
    have f_Surjective : f.Surjective := by
      intro x'
      let x := x' - f 0
      specialize p x (-f x)
      simp at p
      use x + f (x + -f x)
      convert p
      ring
    -- Let $d$ be a zero of $f$.
    rcases f_Surjective 0 with ⟨d, f_d_eq_0⟩
    -- From $P(d, 0)$ we get $0=d+f(0)$, thus $-f(0)$ is the only zero of $f$.
    have : - f 0 = d := by
      specialize p d 0
      simp [f_d_eq_0] at p
      linarith
    -- "only" needs not to be proved here
    have f_minus_f_0_eq_0 : f (- f 0) = 0 := by
      rw [this, f_d_eq_0]
    /-
    From $P(0, y)$ we get

    $$ f(f(y))=f(y+f(0)) $$
    -/
    have f_f_y_eq : ∀ y, f (f y) = f (y + f 0) := by
      intro y
      specialize p 0 y
      simp at p
      convert p using 2
      ring
    -- From $P(-f(0), y+f(0))$ we get $f(f(y)-f(0))=-f(0)+f(y+f(0))$. Using (1), we get $f(f(y)-f(0))=-f(0)+f(f(y))$, or equivalently $f(f(y))=f(f(y)-f(0))+f(0)$.
    have : ∀ y, f (f y) = f (f y - f 0) + f 0 := by
      intro y
      specialize p (-f 0) (y + f 0)
      simp at p
      rw [show -f 0 + f y = f y - f 0 by ring] at p
      simp [f_minus_f_0_eq_0] at p
      rw [←f_f_y_eq] at p
      linarith
    /-
    Since $f$ is surjective, we can replace $f(y)$ by $y$ to obtain

    $$ f(y)=f(y-f(0))+f(0) $$
    -/
    have : ∀ y, f y = f (y - f 0) + f 0 := by
      intro y
      rcases f_Surjective y with ⟨x, f_x_eq_y⟩
      specialize this x
      rw [f_x_eq_y] at this
      exact this
    -- Replacing $y$ by $y+f(0)$ to the right, we get $f(y+f(0))=f(y)+f(0)$.
    have : ∀ y, f (y + f 0) = f y + f 0 := by
      intro y
      specialize this (y + f 0)
      simp at this
      exact this
    /-
    However, applying (1) to the left side gives us

    $$ f(f(y))=f(y)+f(0) $$
    -/
    have : ∀ y, f (f y) = f y + f 0 := by
      intro y
      specialize this y
      specialize f_f_y_eq y
      linarith
    -- Once again, using surjectivity we conclude that $f(y)=y+f(0)$ for every real number $y$. Thus, any function $f$ which is a solution is of the form $f(y)=y+c$ for some real number $c$. It's easy to check that all such functions satisfy the problem's condition.
    use f 0
    intro x
    rcases f_Surjective x with ⟨w, f_w_eq_x⟩
    specialize this w
    rw [f_w_eq_x] at this
    exact this
  . rintro ⟨c, f_eq⟩ x y
    repeat rw [f_eq]
    ring
