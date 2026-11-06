import Mathlib
/- Let $f$ be function defined from the set $\{(x, y): x, y$ reals, $x y \neq 0\}$ in to the set of all positive real numbers such that

(i) $\quad f(x y, z)=f(x, z) f(y, z)$, for all $x, y \neq 0$;

(ii) $\quad f(x, y z)=f(x, y) f(x, z)$, for all $x, y \neq 0$;

(iii) $\quad f(x, 1-x)=1$, for all $x \neq 0,1$.

Prove that

(a) $\quad f(x, x)=f(x,-x)=1$, for all $x \neq 0$;

(b) $\quad f(x, y) f(y, x)=1$, for all $x, y \neq 0$. -/
theorem algebra_607883 {f : ℝ → ℝ → ℝ} (h : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → f x y > 0)(h1 : ∀ x y z, x ≠ 0 → y ≠ 0 → z ≠ 0 → f (x * y) z = f x z * f y z) (h2 : ∀ x y z, x ≠ 0 → y ≠ 0 → z ≠ 0 → f x (y * z) = f x y * f x z) (h3: ∀ x, x ≠ 0 → x ≠ 1 → f x (1 - x) = 1) : (∀ x, x ≠ 0 → f x x = 1 ∧ f x (-x) = 1) ∧ (∀ x y, x ≠ 0 → y ≠ 0 → f x y * f y x = 1):= by
  -- Proving that f(1,z) = 1 for all z ≠ 0
  have h4 : ∀ z : ℝ, z ≠ 0 → f 1 z = 1:= by
    intro z hz
    specialize h1 1 1 z (by simp) (by simp) hz
    simp at h1
    specialize h 1 z (by simp) hz
    replace h1 : f 1 z * (f 1 z - 1) = 0:= by linarith
    replace h : f 1 z ≠ 0:= by linarith
    simp [h] at h1
    linarith

  -- Proving that f(z,1) = 1 for all z ≠ 0
  have h6 : ∀ z : ℝ, z ≠ 0 → f z 1 = 1:= by
    intro z hz
    specialize h2 z 1 1 hz (by simp) (by simp)
    simp at h2
    specialize h z 1 hz (by simp)
    replace h2 : f z 1 * (f z 1 - 1) = 0:= by linarith
    replace h : f z 1 ≠ 0:= by linarith
    simp [h] at h2
    linarith

  -- Proving that f(z,-1) = 1 for all z ≠ 0
  have h7 : ∀ z : ℝ, z ≠ 0 → f z (-1) = 1:= by
    intro z hz
    specialize h2 z (-1) (-1) hz (by linarith) (by linarith)
    simp at h2
    rw [h6 z hz] at h2
    replace h2 : (f z (-1) - 1) * (f z (-1) + 1) = 0:= by linarith
    specialize h z (-1) hz (by linarith)
    replace h : f z (-1) + 1 ≠ 0:= by linarith
    simp [h] at h2
    linarith

  -- Proving that f(x,1/y) = 1/f(x,y) for all x,y ≠ 0
  have g1 : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → f x (1 / y) = 1 / f x y:= by
    intro x y hx hy
    specialize h2 x y (1 / y) hx hy (by exact one_div_ne_zero hy)
    rw [show y * (1 / y) = 1 by field_simp [hy]] at h2
    rw [h6 x hx] at h2
    specialize h x y hx hy
    field_simp
    linarith

  -- Proving that f(1/x,y) = 1/f(x,y) for all x,y ≠ 0
  have g2 : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → f (1 / x) y = 1 / f x y:= by
    intro x y hx hy
    specialize h1 x (1 / x) y hx (by exact one_div_ne_zero hx) hy
    rw [show x * (1 / x) = 1 by field_simp] at h1
    rw [h4 y hy] at h1
    specialize h x y hx hy
    field_simp
    linarith

  -- Proving part (a): f(x,x) = 1 and f(x,-x) = 1 for all x ≠ 0
  have g3 : ∀ (x : ℝ), x ≠ 0 → f x x = 1 ∧ f x (-x) = 1:= by
    intro x hx
    by_cases hx1 : x = 1
    .
      subst x
      refine ⟨h6 1 (by simp) , h4 (-1) (by simp)⟩
    .
      -- Proving f(x,-x) = 1 for the case where x ≠ 1
      have g3 : f x (-x) = 1:= by
        have g3 : 1 / x ≠ 0:= by exact one_div_ne_zero hx
        have g4 : 1 / x ≠ 1:= by
          by_contra H
          field_simp at H
          subst x
          simp at hx1
        have g:= h3 x hx hx1
        specialize h3 (1 / x) g3 g4
        -- Proving that f(x,y) = f(1/x,1/y) for all x,y ≠ 0
        have g5 : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → f x y = f (1 / x) (1 / y):= by
          intro x y hx hy
          specialize g1 x (1 / y) hx (by exact one_div_ne_zero hy)
          specialize g2 x (1 / y) hx (by exact one_div_ne_zero hy)
          field_simp at g1 g2
          linarith
        have g6 : 1 - 1 / x ≠ 0:= by
          by_contra H
          field_simp at H
          replace H : x = 1:= by linarith
          subst x
          simp at hx1
        specialize g5 (1 / x) (1 - 1 / x) (by exact one_div_ne_zero hx) g6
        rw [show 1 / (1 / x) = x by field_simp] at g5
        rw [show 1 / (1 - 1 / x) = x / (x - 1) by field_simp] at g5
        rw [h3] at g5
        replace g5 : f x (x / (x - 1)) * f x (1 - x) = 1:= by
          rw [g]
          linarith
        replace g3 : x / (x - 1) ≠ 0:= by
          by_contra H
          simp at H
          rcases H with H | H
          .
            trivial
          .
            replace H : x = 1:= by linarith
            trivial
        replace g4 : 1 - x ≠ 0:= by
          by_contra H
          replace H : x = 1:= by linarith
          trivial
        rw [←h2 x (x / (x - 1)) (1 - x) hx g3 g4] at g5
        replace g4 : x - 1 ≠ 0:= by
          by_contra H
          replace H : x = 1:= by linarith
          trivial
        rw [show x / (x - 1) * (1 - x) = -x by field_simp ; linarith] at g5
        exact g5
      refine ⟨?_, g3⟩
      -- Proving f(x,x) = 1 using the result f(x,-x) = 1
      specialize h2 x (-x) (-1) hx (by exact neg_ne_zero.mpr hx) (by linarith)
      simp at h2
      rw [h2, g3, h7 x hx]
      simp

  -- Combining the results to prove both parts (a) and (b)
  refine ⟨g3, ?_⟩
  -- Proving part (b): f(x,y)f(y,x) = 1 for all x,y ≠ 0
  intro x y hx hy
  have g4 : f x y = f x y * f x x:= by
    rw [(g3 x hx).1]
    simp
  have g5 : f y x = f y x * f y y:= by
    rw [(g3 y hy).1]
    simp
  rw [g4, g5]
  rw [←h2 x y x hx hy hx]
  rw [←h2 y x y hy hx hy]
  rw [show y * x = x * y by ring]
  rw [←h1 x y (x * y) hx hy (by exact mul_ne_zero hx hy)]
  rw [(g3 (x * y) (by exact mul_ne_zero hx hy)).1]
