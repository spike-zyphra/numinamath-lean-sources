import Mathlib

open Real Set
open scoped Real

/- Given the function $f(x) = \cos 2x + 2\sin x$,

(Ⅰ) Find the value of $f\left(-\frac{\pi}{6}\right)$;

(Ⅱ) Determine the range of $f(x)$.-/
theorem algebra_9048 {f : ℝ → ℝ} (hf : f = λ x => cos (2 * x) + 2 * sin x) :
    f (-π / 6) = -1 / 2 ∧ ∀ x, f x ∈ Icc (-3) (3 / 2) := by
  constructor
  --(Ⅰ) $f\left(-\frac{\pi}{6}\right) = \cos\left(-\frac{\pi}{3}\right) + 2\sin\left(-\frac{\pi}{6}\right)$
  --$= \frac{1}{2} + 2 \times \left(-\frac{1}{2}\right)$
  --$= -\frac{1}{2}$;
  --So, $f\left(-\frac{\pi}{6}\right) = \boxed{-\frac{1}{2}}$.
  . simp [hf]
    rw [show 2 * (-π / 6) = - (π / 3) by ring, Real.cos_neg, Real.cos_pi_div_three]
    rw [neg_div, Real.sin_neg, Real.sin_pi_div_six]
    norm_num
  --(Ⅱ) $f(x) = (1-2\sin^2x) + 2\sin x = -2\left(\sin x- \frac{1}{2}\right)^2 + \frac{3}{2}$,
  --Therefore, when $x = \frac{\pi}{6} + 2k\pi$ or $x = \frac{5\pi}{6} + 2k\pi$, $k \in \mathbb{Z}$, $f(x)$ reaches its maximum value $\frac{3}{2}$;
  --When $x = -\frac{\pi}{2} + 2k\pi$, $k \in \mathbb{Z}$, $f(x)$ reaches its minimum value $-3$;
  --Therefore, the range of $f(x)$ is $\boxed{[-3, \frac{3}{2}]}$.
  intro x
  simp only [hf]
  rw [Real.cos_two_mul, Real.cos_sq', show _ - 1 + 2 * sin x = -2*(sin x - 1 / 2)^2+3/2 by ring]
  set y := sin x - 1 / 2 with hy
  have range_y : y ∈ Icc (-1 - 1 / 2) (1 - 1 / 2) := by
    simp [hy]
    rw [← mem_Icc]
    exact Real.sin_mem_Icc _
  rw [mem_Icc] at range_y ⊢
  constructor <;> nlinarith
