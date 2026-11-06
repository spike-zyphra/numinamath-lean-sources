import Mathlib
/-
Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ waarvoor geldt dat $$ f(a-b) f(c-d)+f(a-d) f(b-c) \leq(a-c) f(b-d) $$ voor alle reële getallen $a, b, c$ en $d$. N.B. rechts van het ongelijkheidsteken staat dus maar één $f$.
-/
/-
The solutions are $f(x)=0$ for all $x$ and $f(x)=x$ for all $x$. For $f(x)=0$, we easily find that equality always holds. For $f(x)=x$, we check that

$$ \begin{aligned} (a-b)(c-d)+(a-d)(b-c) & =a c-a d-b c+b d+a b-a c-b d+c d \ & =-a d-b c+a b+c d \ & =(a-c)(b-d), \end{aligned} $$

so equality also holds in this case. Now we show that these are the only two solutions.

Substituting $a=b=c=d=0$ gives us that $2 f(0)^{2} \leq 0$, which means that $f(0)=0$.

Next, we substitute $b=a-x, c=a$ and $d=a-y$, so that $a-b=x, a-c=0$ and $a-d=y$. Then we find that

$$ f(y)(f(x)+f(-x)) \leq 0 $$

Suppose there is a $y$ such that $f(y) \neq 0$. If we then substitute $x=y$ into the equation above and move one of the terms to the right, we find that

$$ 0&lt;f(y)^{2} \leq-f(y) f(-y) $$

This means that one of the two values $f(y)$ and $f(-y)$ is positive and the other is negative. Suppose without loss of generality that $f(y)$ is positive.

Given arbitrary $a$ and $y$, now substitute $b=a, c=0$ and $d=a-y$. Then we find that $f(y) f(a) \leq a f(y)$. Dividing by $f(y)$, we get $f(a) \leq a$. However, if we had substituted $b=a$, $c=0$ and $d=a+y$, we would have found that $f(-y) f(a) \leq a f(-y)$. Since $f(-y)$ is negative, the inequality sign flips when we divide by $f(-y)$, so we also find that $f(a) \geq a$. We conclude that $f(a)=a$ for all real $a$.

Thus, $f$ is the zero function or $f(a)=a$ for all real $a$, both of which we checked at the beginning.

Remark. By applying the argument of the last paragraph to equation (1), we can also find as an intermediate step that $f(x)=-f(-x)$ for all $x$.
-/
theorem algebra_32769 {f : ℝ → ℝ} : (∀ a b c d : ℝ, f (a - b) * f (c - d) + f (a - d) * f (b - c) ≤ (a - c) * f (b - d)) ↔ (∀ x : ℝ, f x = 0) ∨ (∀ x : ℝ, f x = x) := by
apply Iff.intro
-- First we prove that every f satisfying the condition must be of the two forms.
intro H
-- We prove that f 0 = 0 and the key lemma that ∀x:ℝ,∀y:ℝ,(f y)*(f x + f (-x))≤0.
have h1 : f 0 = 0 := by
  have h := H 0 0 0 0
  simp at h
  exact real_inner_self_nonpos.mp h
have h2 : ∀x:ℝ,∀y:ℝ,(f y)*(f x + f (-x))≤0 := by
  intro x y
  have h := H 0 (-x) 0 (-y)
  simp at h
  calc
    f y * (f x + f (-x)) = f x * f y + f y * f (-x) := by ring
    _ ≤ 0 := by exact h
-- f x = 0 everywhere is just the first answer.
by_cases p : ∀x:ℝ,f x = 0
left
exact p
-- If some y makes f y ≠ 0, we prove that the second answer is correct.
right
intro x
push_neg at p
obtain ⟨y,hy⟩:=p
-- In fact, f y and f (-y) must have different signatures, so we prove by cases.
by_cases q1 : f y > 0
have q2 : f (-y) < 0 := by
  have h := h2 y y
  have hh1 : f y * (f y + f (-y)) ≤ (f y) * 0 := by simp; exact h
  have hh : f y + f (-y) ≤ 0 := le_of_mul_le_mul_left hh1 q1
  calc
    f (-y) ≤ - (f y) := by exact le_neg_iff_add_nonpos_left.mpr hh
    _ < 0 := by exact neg_neg_iff_pos.mpr q1
have hleq : f x ≤ x := by
  have h := H x x 0 (x-y)
  simp at h
  rw [h1] at h
  simp at h
  rw [mul_comm] at h
  exact le_of_mul_le_mul_right h q1
have hgeq : f x ≥ x := by
  have h := H x x 0 (x+y)
  simp at h
  rw [h1] at h
  simp at h
  rw [mul_comm] at h
  exact (mul_le_mul_right_of_neg q2).mp h
exact le_antisymm hleq hgeq
-- The other case is proven in the same manner
have p1 : f y < 0 := by
  simp at q1
  exact lt_of_le_of_ne q1 hy
have p2 : f (-y) > 0 := by
  have h := h2 y y
  have hh1 : (- f y) * (f y + f (-y)) ≥ (- f y) * 0 := by simp; exact h
  have hh2 : (- f y) > 0 := by exact Left.neg_pos_iff.mpr p1
  have hh : f y + f (-y) ≥ 0 := le_of_mul_le_mul_left hh1 hh2
  calc
    f (-y) ≥ - f y := by exact neg_le_iff_add_nonneg'.mpr hh
    _ > 0 := by exact hh2
have hleq : f x ≤ x := by
  have h := H x x 0 (x+y)
  simp at h
  rw [h1] at h
  simp at h
  rw [mul_comm] at h
  exact le_of_mul_le_mul_right h p2
have hgeq : f x ≥ x := by
  have h := H x x 0 (x-y)
  simp at h
  rw [h1] at h
  simp at h
  rw [mul_comm] at h
  exact (mul_le_mul_right_of_neg p1).mp h
exact le_antisymm hleq hgeq
-- Then we prove that these two given answers really fits the condition.
intro h a b c d
cases h with
| inl  hl =>
  rw [hl (a-b), hl (c-d), hl (a-d), hl (b-c), hl (b-d)]
  simp
| inr hr =>
  rw [hr (a-b), hr (c-d), hr (a-d), hr (b-c), hr (b-d)]
  calc
    (a - b) * (c - d) + (a - d) * (b - c) = (a - c) * (b - d) := by ring
    _ ≤ (a - c) * (b - d) := by exact Preorder.le_refl ((a - c) * (b - d))
