import Mathlib


/- The numbers $x$ and $y$ are inversely proportional. When the sum of $x$ and $y$ is 42, $x$ is twice $y$. What is the value of $y$ when $x=-8$? -/
theorem algebra_14758
    (x y : ℝ → ℝ)
    (hinv : ∃ k, (∀ t, x t * y t = k))
    (h : ∀ t, x t + y t = 42 → x t = 2 * y t)
    (h' : ∃ t, x t + y t = 42) :
    ∀ t, x t = -8 → y t = -49 := by

  obtain ⟨t, ht⟩ := h'

  -- We know that when $x+y=42$, $x=2y$. Substituting $2y$ in for $x$ in the first equation gives $3y=42$, or $y=14$.
  have r1 : y t = 14 := by
    specialize h t ht
    rw [h] at ht
    linarith

  -- The value of $x$ is then $2(14)=28$.
  have r2 : x t = 28 := by
    linarith

  -- Since $x$ and $y$ are inversely proportional, the product $xy$ is constant. Let $xy=k$. When $x=28$ and $y=14$, $k=(28)(14)=392$.
  obtain ⟨k, hinv⟩ := hinv
  have r3 : k = 392 := by
    specialize hinv t
    rw [← hinv, r1, r2]
    norm_num

  -- Therefore, when $x=-8$, $(-8)y=392$, giving $y=\boxed{-49}$.
  intro t hxt
  specialize hinv t
  rw [r3, hxt] at hinv
  linarith
