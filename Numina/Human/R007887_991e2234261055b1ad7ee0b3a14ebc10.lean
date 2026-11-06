import Mathlib

/- Gegeven is een verzameling $A$ van functies $f: \mathbb{R} \rightarrow \mathbb{R}$. Voor alle $f_{1}, f_{2} \in A$ bestaat er een $f_{3} \in A$ zodat

$$
f_{1}\left(f_{2}(y)-x\right)+2 x=f_{3}(x+y)
$$

voor alle $x, y \in \mathbb{R}$. Bewijs dat voor alle $f \in A$ geldt:

$$
f(x-f(x))=0
$$

voor alle $x \in \mathbb{R}$. -/
theorem algebra_606258 {A : Set (ℝ → ℝ)} (hA : ∀ f1 ∈ A, ∀ f2 ∈ A,
    ∃ f3 ∈ A, ∀ x y, f1 (f2 y - x) + 2 * x = f3 (x + y)) :
    ∀ f ∈ A, ∀ x, f (x - f x) = 0 := by

  -- Substituting $x=-y$ now gives that $$ f_{1}\left(f_{2}(y)+y\right)=f_{3}(0)+2y=f_{1}\left(f_{2}(0)\right)+2y $$
  have hA_x_eq_neg_y: ∀ f1 ∈ A, ∀ f2 ∈ A, ∀ y, f1 (f2 y + y)  = f1 (f2 0) + 2 * y := by
    intro f1 f1_in_A f2 f2_in_A y
    specialize hA f1 f1_in_A f2 f2_in_A
    obtain ⟨f3, f3_in_A, h3⟩ := hA
    have h3' := h3 (-y) y
    simp at h3'
    ring_nf at h3'
    -- substituting $x=0$, $y=0$ gives that $$ f_{1}\left(f_{2}(0)\right)=f_{3}(0) $$
    have h3'' := h3 0 0
    simp at h3''
    rw [<-h3''] at h3'
    rw [<-h3', <-sub_eq_zero]
    ring_nf
  -- substituting $x=f_{2}(y)$ gives that $$ f_{1}(0)+2f_{2}(y)=f_{3}\left(f_{2}(y)+y\right) $$
  have hA_x_eq_f2y: ∀ f1 ∈ A, ∀ f2 ∈ A, ∃ f3 ∈ A, ∀ y, f1 0 + 2 * f2 y = f3 (f2 y + y) := by
    intro f1 f1_in_A f2 f2_in_A
    specialize hA f1 f1_in_A f2 f2_in_A
    obtain ⟨f3, f3_in_A, h3⟩ := hA
    use f3
    constructor
    exact f3_in_A
    intro y
    have h3' := h3 (f2 y) y
    simp at h3'
    exact h3'
  -- we have seen before that we can write $f_{3}\left(f_{2}(y)+y\right)$ as $2y+f_{3}\left(f_{2}(0)\right)$
  have hA_x_eq_2y: ∀ f1 ∈ A, ∀ f2 ∈ A, ∃ f3 ∈ A, ∀ y, f1 0 + 2 * f2 y = f3 (f2 0) + 2 * y := by
    intro f1 f1_in_A f2 f2_in_A
    specialize hA_x_eq_f2y f1 f1_in_A f2 f2_in_A
    obtain ⟨f3, f3_in_A, h3⟩ := hA_x_eq_f2y
    use f3
    constructor
    exact f3_in_A
    intro y
    specialize h3 y
    rw [hA_x_eq_neg_y f3 f3_in_A f2 f2_in_A] at h3
    exact h3

  -- so every $f \in A$ is of the form $f(x)=x+d$ with $d$ a constant
  have : ∀ f ∈ A, ∃ d: ℝ, ∀ x:ℝ, f x = x + d := by
    intro f2 f2_in_A
    specialize hA_x_eq_2y f2 f2_in_A f2 f2_in_A
    obtain ⟨f3, f3_in_A, h3⟩ := hA_x_eq_2y
    use (f3 (f2 0) - f2 0) / 2
    intro y
    specialize h3 y
    linear_combination h3 / 2

  -- since we know that $f(x)=x+d$ for all $f \in A$, we can substitute this in the original equation
  intro f f_in_A x
  specialize this f f_in_A
  obtain ⟨d, h⟩ := this
  rw [h, h]
  simp
