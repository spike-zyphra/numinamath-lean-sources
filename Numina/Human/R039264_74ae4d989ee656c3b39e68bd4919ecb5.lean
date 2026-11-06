import Mathlib

/- Vind alle functies $f: \mathbb{R} \backslash\{0\} \rightarrow \mathbb{R}$ waarvoor geldt:

$$
x f(x y)+f(-y)=x f(x)
$$

voor alle reële $x, y$ ongelijk aan 0 .-/
theorem algebra_605246 : {f : ℝ → ℝ | ∀ x y, x ≠ 0 → y ≠ 0 → x * f (x * y) + f (-y) = x * f x} =
    {f : ℝ → ℝ | ∃ c, ∀ x, x ≠ 0 → f x = c + c / x} := by
  ext f
  constructor
  . intro hf
    rw [Set.mem_setOf] at hf ⊢
    -- Substitute $x=1$, which gives $f(y)+f(-y)=f(1)$, or $f(-y)=f(1)-f(y)$ for all $y$.
    have hfy {y : ℝ} (hyne : y ≠ 0) : f y + f (-y) = f 1 := by
      specialize hf 1 y (by norm_num) hyne
      simp at hf
      exact hf
    -- Now substitute $y=-1$, which gives $x f(-x)+f(1)=x f(x)$.
    have hfx {x : ℝ} (hxne : x ≠ 0) : x * f (-x) + f 1 = x * f x := by
      specialize hf x (-1) hxne (by norm_num)
      simp at hf
      exact hf
    -- If we substitute $f(-x)=$ $f(1)-f(x)$ here,
    -- we get $x(f(1)-f(x))+f(1)=x f(x)$,
    -- so $x f(1)+f(1)=2 x f(x)$.
    have h {x : ℝ} (hxne : x ≠ 0) : x * f 1 + f 1 = 2 * x * f x := by
      suffices x * (f 1 - f x) + f 1 = x * f x by linarith
      have : f (-x) = f 1 - f x := by
        suffices f x + f (-x) = f 1 by linarith
        exact hfy hxne
      rw [← this]
      exact hfx hxne
    -- We see that $f$ is of the form $f(x)=c+\frac{c}{x}$ for some $c \in \mathbb{R}$.
    use f 1 / 2
    -- We see that $f$ is of the form $f(x)=c+\frac{c}{x}$ for some $c \in \mathbb{R}$.
    -- We check this family of functions.
    -- On the left, we have $x f(x y)+f(-y)=x\left(c+\frac{c}{x y}\right)+c+\frac{c}{-y}=x c+c$
    -- and on the right, we have $x f(x)=x\left(c+\frac{c}{x}\right)=x c+c$.
    -- These two are equal, so this function satisfies for all $c \in \mathbb{R}$.
    intro x hx
    field_simp
    specialize h hx
    apply_fun (2 * ·) at h
    linear_combination -h
  . -- Verify that `f(x)=c+c/x` is solution.
    intro ⟨c, hc⟩
    rw [Set.mem_setOf]
    intro x y hx hy
    have : -y ≠ 0 := fun h => by absurd hy; linear_combination -h
    rw [hc _ (by positivity), hc _ (by assumption), hc _ (by assumption)]
    field_simp
    ring
