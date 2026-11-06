import Mathlib

open Real Set
open scoped Real

/-
Problem

The minimum value of the function $f(x) = \sqrt{2} \sin x (\cos x + \sin x) - \frac{\sqrt{2}}{2}$ in the interval $[0, \frac{\pi}{2}]$ is __________.
-/

/-
Solution

Consider the function $f(x) = \sqrt{2} \sin x (\cos x + \sin x) - \frac{\sqrt{2}}{2}$. Using trigonometric identities, we can rewrite $f(x)$ as:
\begin{align*}
f(x) &= \sqrt{2}\sin x \cos x + \sqrt{2}\sin^2 x - \frac{\sqrt{2}}{2} \\
     &= \frac{\sqrt{2}}{2}\sin 2x + \frac{\sqrt{2}}{2}(1 - \cos 2x) - \frac{\sqrt{2}}{2} \\
     &= \frac{\sqrt{2}}{2}\sin 2x - \frac{\sqrt{2}}{2}\cos 2x.
\end{align*}
Let's use the angle sum identity for sine to combine the terms:
$$ f(x) = \sin\left(2x - \frac{\pi}{4}\right). $$

Now, since $x \in \left[0, \frac{\pi}{2}\right]$, it follows that $2x \in [0, \pi]$, and therefore $2x - \frac{\pi}{4} \in \left[-\frac{\pi}{4}, \frac{3\pi}{4}\right]$. The sine function reaches its minimum value of $-1$ when its argument is an odd multiple of $\frac{\pi}{2}$, but this interval includes the value $-\frac{\pi}{4}$ where the sine function has the value of $-\frac{\sqrt{2}}{2}$. Hence, the minimum value occurs when $2x - \frac{\pi}{4} = -\frac{\pi}{4}$ or when $x = 0$:
$$ f(x) = \sin\left(-\frac{\pi}{4}\right) = -\frac{\sqrt{2}}{2}. $$

Therefore, the minimum value of $f(x)$ on the interval $\left[0, \frac{\pi}{2}\right]$ is $\boxed{-\frac{\sqrt{2}}{2}}$.
-/
theorem algebra_9092 {f : ℝ → ℝ}
  (hf : f = λ x => sqrt 2 * sin x * (cos x + sin x) - sqrt 2 / 2)
  (I : Set ℝ) (hI : I = Icc 0 (π/2)) :
  IsLeast (image f I) (-sqrt 2 / 2) := by
    have hf : f = λ x => sin (2 * x - π / 4) := by
      rw [hf]
      funext x
      calc sqrt 2 * sin x * (cos x + sin x) - sqrt 2 / 2
        _ = sqrt 2 * (sin x * cos x + sin x * sin x) - sqrt 2 / 2 := by rw [mul_assoc, left_distrib]
        _ = sqrt 2 * (sin (2 * x)/2 + sin x ^ 2) - sqrt 2 / 2 := by rw [sin_two_mul]; ring
        _ = sqrt 2 * (sin (2 * x)/2 + sin x ^ 2 + 1 - (sin x ^ 2 + cos x ^ 2)) - sqrt 2 / 2 := by simp
        _ = sqrt 2 * (sin (2 * x)/2 - cos x ^ 2 + 1) - sqrt 2 / 2 := by ring
        _ = sqrt 2 * (sin (2 * x)/2 - cos x ^ 2 + 1) - sqrt 2 / 2 := by ring
        _ = sqrt 2 * (sin (2 * x)/2 - (cos (2 * x) + 1) / 2 + 1) - sqrt 2 / 2 := by rw [cos_two_mul]; ring
        _ = sqrt 2 / 2 * (sin (2 * x) - cos (2 * x)) := by ring
        _ = sin (2 * x) * cos (π / 4)  - cos (2 * x) * sin (π / 4) := by simp; ring
        _ = sin ((2 * x) - π / 4) := by rw [Real.sin_sub]

    -- substitution (2 * x) - π / 4 to x
    let g := λ x => (2 * x) + (- π / 4)
    let hg : g = λ x => (2 * x) + (- π / 4):= by simp

    let sin_i := Icc (- π / 4) (3*π/4)
    let hsin_i : sin_i = Icc (- π / 4) (3*π/4) := by simp

    have image_g : image g I = sin_i := by
      rw [hI, hg, hsin_i]
      rw [Set.image_affine_Icc']
      ring_nf
      simp
    have comp_f: f = sin ∘ g := by
      rw [hf, hg]
      unfold Function.comp
      funext x
      ring_nf
    have image_f : image f I = image sin sin_i := by rw [comp_f, Set.image_comp, image_g]
    rw [image_f]

    -- split the interval
    let sin_i1 := Icc (- π / 4) (π/2)
    let hsin_i1: sin_i1 = Icc (- π / 4) (π/2) := by simp
    let sin_i2 := Icc (π/2) (3 * π / 4)
    let hsin_i2 : sin_i2 = Icc (π/2) (3 * π / 4) := by simp

    -- some order relations
    have pi_div_2_le_3mul_pi_div_4: π / 2 ≤ 3 * π / 4 := by {
      have pi_div_2_lt_3mul_pi_div_4: π / 2 < 3 * π / 4 := by {
        rw [<- sub_lt_zero]
        ring_nf
        have h1: -(1:ℝ) /4<0:= by linarith
        exact mul_neg_of_pos_of_neg pi_pos h1
      }
      exact le_of_lt pi_div_2_lt_3mul_pi_div_4
    }
    have neg_pi_div_4_le_pi_div_2 : - π / 4 <= π/2 := by {
      have neg_pi_div_4_lt_pi_div_2: - π / 4 < π/2 := by {
        rw [<- sub_lt_zero]
        ring_nf
        have h1: -(3:ℝ) /4<0:= by linarith
        exact mul_neg_of_pos_of_neg pi_pos h1
      }
      exact le_of_lt neg_pi_div_4_lt_pi_div_2
    }

    have split_i: sin '' sin_i = (sin '' sin_i1) ∪ (sin '' sin_i2) := by {
      rw [<- Set.image_union, hsin_i, hsin_i1, hsin_i2]
      rw [Set.Icc_union_Icc_eq_Icc]
      exact neg_pi_div_4_le_pi_div_2
      exact pi_div_2_le_3mul_pi_div_4
    }

    have dev: ∀ x: ℝ, deriv sin x = cos x := by {
      intros x
      simp
    }
    -- find the minimum num in the fiest interval
    have least1: IsLeast (sin '' sin_i1) (sin (- π / 4)) := by {
      -- prove sin is monotone in the first interval
      have dev_nonneg: ∀ x ∈ interior sin_i1, 0 ≤ deriv sin x := by {
        intros x hx
        rw [(dev x)]
        rw [hsin_i1] at hx
        simp at hx
        have in_icc :  x ∈ Icc (-(π / 2)) (π / 2) := by constructor <;> linarith
        exact Real.cos_nonneg_of_mem_Icc in_icc
      }
      have monotone_sin_i1 : MonotoneOn sin sin_i1 :=
        monotoneOn_of_deriv_nonneg (convex_Icc (- π / 4) (π/2)) Real.continuousOn_sin (DifferentiableOn.sin (differentiableOn_id)) dev_nonneg
      exact MonotoneOn.map_isLeast monotone_sin_i1 (isLeast_Icc neg_pi_div_4_le_pi_div_2)
    }
    -- find the minimum num in the fiest interval
    have least2: IsLeast (sin '' sin_i2) (sin (3 * π / 4)) := by {
      -- prove sin is antitone in the second interval
      have dev_nonpos: ∀ x ∈ interior sin_i2, deriv sin x ≤ 0 := by {
        intros x hx
        rw [(dev x)]
        rw [hsin_i2] at hx
        simp at hx
        have h1 : Real.pi / 2 < x := by linarith
        have h2 : x < Real.pi + Real.pi / 2 := by linarith
        exact le_of_lt (Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2)
      }
      have antitone_sin_i2 : AntitoneOn sin sin_i2 :=
        antitoneOn_of_deriv_nonpos (convex_Icc (π/2) (3 * π / 4)) Real.continuousOn_sin (DifferentiableOn.sin (differentiableOn_id)) dev_nonpos
      exact AntitoneOn.map_isGreatest antitone_sin_i2 (isGreatest_Icc pi_div_2_le_3mul_pi_div_4)
    }

    have least: IsLeast ((sin '' sin_i1) ∪ (sin '' sin_i2)) (sin (- π / 4) ⊓ sin (3 * π / 4)) := IsLeast.union least1 least2
    rw [<- split_i] at least
    have sin1: sin (-π / 4) = - √2 / 2 := by {
      calc sin (-π / 4)
      _ = sin (-(π / 4)) := by ring_nf
      _ = - sin (π / 4) := by rw [sin_neg]
      _ = - √2 / 2 := by rw [Real.sin_pi_div_four]; ring_nf
    }
    have sin_eq: sin (3 * π / 4) = √2 / 2 := by {
      calc sin (3 * π / 4)
      _ = sin (π / 4 + π / 2) := by ring_nf
      _ = cos (π / 4) := by rw [sin_add_pi_div_two]
      _ = √2 / 2 := by rw [Real.cos_pi_div_four]
    }
    rw [sin1, sin_eq] at least
    have h1: -√2 / 2 < √2 / 2 := by {
      rw [<-sub_lt_zero]
      ring_nf
      simp
    }
    have min_sin: -√2 / 2 ⊓ √2 / 2 = -√2 / 2 := min_eq_left_of_lt h1
    rw [min_sin] at least
    exact least
