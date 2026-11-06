import Mathlib

/-Let \[f(n) = \left\{
\begin{array}{cl}
n^2-2 & \text{ if }n<0, \\
2n-20 & \text{ if }n \geq 0.
\end{array}
\right.\]What is the positive difference between the two values of $a$ that satisfy the equation $f(-2)+f(2)+f(a)=0$?-/
theorem algebra_11092 {f : ℝ → ℝ}
    (hf : ∀ x, x < 0 → f x = x ^ 2 - 2)
    (hf' : ∀ x, x ≥ 0 → f x = 2 * x - 20) (a1 a2 : ℝ)
    (ha1 : f (-2) + f 2 + f a1 = 0) (ha2 : f (-2) + f 2 + f a2 = 0)
    (ha12 : a1 ≠ a2) : |a1 - a2| = 21 := by
  -- We begin by finding $f(-2)$ and $f(2)$.
  -- Since $-2<0$, we have that $f(-2)=(-2)^2-2=2$
  have f_neg2 : f (-2) = 2 := by
    rw [hf (-2) (by linarith)]
    linarith
  -- and since $2 \geq 0$, we have that $f(2)=2(2)-20=-16$.
  have f_2 : f 2 = -16 := by
    rw [hf' 2 (by linarith)]
    linarith

  rw [f_neg2, f_2] at ha1 ha2
  -- Now we can substitute these values back into our equation $f(-2)+f(2)+f(a)=0$ to get $2 + (-16) + f(a) = 0$, so $f(a)=14$.
  have ha1 : f a1 = 14 := by linarith
  have ha2 : f a2 = 14 := by linarith

  -- Our next step is to find all values of $a$ such that $f(a)=14$.
  by_cases ha1': a1 < 0
  . -- Our first equation $f(a)=a^2-2=14$ yields that $a= \pm 4$, but $a<0$ so $a=-4$ is the only solution.
    rw [hf a1 ha1'] at ha1
    have ha1 : (a1 - 4) * (a1 + 4) = 0 := by linarith
    simp at ha1
    rcases ha1 with (r | r₁)
    . -- a1 = 4, which is not possible since a1 < 0.
      linarith
    -- a1 = -4
    -- then, if a2 < 0, we will get a2 = -4, which contradicts a1 ≠ a2.
    have r₁: a1 = -4 := by linarith
    have ha2' : a2 ≥ 0 := by
      by_contra ha2'_neg
      simp at ha2'_neg
      rw [hf a2 ha2'_neg] at ha2
      have ha2 : (a2 - 4) * (a2 + 4) = 0 := by linarith
      simp at ha2
      rcases ha2 with (r | r)
      . -- a2 = 4, but, we are in `by_contra`, ha2'_neg: a2 < 0
        linarith
      . -- a2 = -4, it is same as a1, which contradicts a1 ≠ a2.
        absurd ha12
        linarith
    rw [hf' a2 ha2'] at ha2
    -- ur second equation $f(a)=2a-20=14$ yields that $a=17$ which is indeed greater than or equal to $0$.
    have r₂: a2 = 17 := by linarith
    -- Thus, our two possible values of $a$ are $-4$ and $17$ and their positive difference is $17 - (-4) = \boxed{21}$.
    rw [r₁, r₂]
    norm_num

  -- a1 ≥ 0, which is similar to the above case, we will get a1 = 17, a2 = -4
  simp at ha1'
  rw [hf' a1 ha1'] at ha1
  have r₁: a1 = 17 := by linarith
  have ha2' : a2 < 0 := by
    by_contra ha2'_neg
    simp at ha2'_neg
    rw [hf' a2 ha2'_neg] at ha2
    have : a1 = a2 := by linarith
    absurd ha12
    exact this
  rw [hf a2 ha2'] at ha2
  have ha2 : (a2 - 4) * (a2 + 4) = 0 := by linarith
  simp at ha2
  rcases ha2 with (r | r₂)
  . -- a2 = 4, but, we are in `by_contra`, ha2'_neg: a2 < 0
    linarith
  have r₂: a2 = -4 := by linarith
  rw [r₁, r₂]
  norm_num
