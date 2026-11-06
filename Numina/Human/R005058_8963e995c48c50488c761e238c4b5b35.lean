import Mathlib
/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ satisfying

$$
f\left(x+y f\left(x^{2}\right)\right)=f(x)+x f(x y)
$$

for all real numbers $x$ and $y$. -/
theorem algebra_605337 (f : ℝ → ℝ) : (∀ x y : ℝ, f (x + y * f (x ^ 2)) = f x + x * f (x * y)) ↔ ((∀ x : ℝ, f x = x) ∨ (∀ x : ℝ, f x = 0)):= by
    constructor
    -- Forward direction: proving that the functional equation implies f(x) = x or f(x) = 0
    .
        intro h
        -- Define proposition P for the functional equation
        set P : ℝ × ℝ → Prop:= fun (x, y) => f (x + y * f (x ^ 2)) = f x + x * f (x * y) with hP
        clear_value P
        replace h : ∀ x y : ℝ, P (x, y):= by
            intro x y
            simp [hP]
            exact h x y
        have h1 : f 0 = 0:= by
          specialize h 1 0
          simp [hP] at h
          exact h
        -- Case split on whether f(x²) ≠ 0 for all x ≠ 0
        by_cases h2 : ∀ x : ℝ, x ≠ 0 → f (x ^ 2) ≠ 0
        -- Case 1: f(x²) ≠ 0 for all x ≠ 0
        .
          -- Prove f(1) = 1
          have h3 : f 1 = 1:= by
            by_contra H
            have h4 : ∃ y : ℝ, 1 + y * f 1 = y:= by
              use (1 / (1 - f 1))
              replace H : 1 - f 1 ≠ 0:= by
                by_contra H1
                replace H1 : f 1 = 1:= by linarith
                trivial
              field_simp
            rcases h4 with ⟨y, hy⟩
            specialize h 1 y
            simp [hP] at h
            rw [hy] at h
            specialize h2 1 (by simp)
            simp at h2
            replace h : f 1 = 0:= by linarith
            trivial
          -- Prove f is odd: f(-x) = -f(x)
          have h4 : ∀ x : ℝ, f (-x) = -f x:= by
            intro x
            by_cases hx : x = 0
            .
              subst x
              simp
              rw [h1]
              linarith
            .
              specialize h2 x hx
              have g1:= h x (-x / (f (x ^ 2)))
              have g2:= h (-x) (x / (f (x ^ 2)))
              simp [hP] at g1 g2
              field_simp at g1 g2
              rw [h1] at g1 g2
              linarith
          -- Prove f is homogeneous of degree 1: f(2x) = 2f(x)
          have h5 : ∀ x : ℝ, f (2 * x) = 2 * f x:= by
            intro x
            by_cases hx : x = 0
            .
              subst x
              simp
              rw [h1]
              linarith
            .
              specialize h2 x hx
              have g1:= h x (x / f (x ^ 2))
              have g2:= h x (-x / f (x ^ 2))
              simp [hP] at g1 g2
              field_simp at g1 g2
              specialize h4 (x * x / f (x ^ 2))
              rw [h1] at g2
              rw [show x + x = 2 * x by ring_nf] at g1
              field_simp at h4
              rw [h4] at g2
              ring_nf at g1 g2
              ring_nf
              linarith
          -- Prove f is additive: f(x + y) = f(x) + f(y)
          have h6 : ∀ x y : ℝ, f x + f y = f (x + y):= by
            intro x y
            by_cases hxy : x + y = 0
            .
              replace hxy : x = -y:= by linarith
              rw [hxy]
              simp
              rw [h1]
              specialize h4 y
              linarith
            .
              have h6 : ∀ x y : ℝ, f (x + y * f (x ^ 2)) + f (x - y * f (x ^ 2)) = f (2 * x):= by
                intro x y
                specialize h5 x
                rw [h5]
                have g1:= h x y
                have g2:= h x (-y)
                simp [hP] at g1 g2
                specialize h4 (x * y)
                rw [h4] at g2
                ring_nf at g1 g2
                ring_nf
                linarith
              specialize h6 ((x + y) / 2) ((y - x) / (2 * f (((x + y) / 2) ^ 2)))
              specialize h2 ((x + y) / 2) (by positivity)
              set t:= f (((x + y) / 2) ^ 2) with ht
              clear_value t
              field_simp at h6
              ring_nf at h6
              field_simp at h6
              linarith
          -- Various functional identities derived from the main equation
          have h7 : ∀ x y : ℝ, f (y * f (x ^ 2)) = x * f (x * y):= by
            intro x y
            specialize h x y
            simp [hP] at h
            specialize h6 x (y * f (x ^ 2))
            rw [←h6] at h
            linarith
          have h8 : ∀ x : ℝ, f (f (x ^ 2)) = x * f x:= by
            intro x
            specialize h7 x 1
            simp at h7
            exact h7
          have h9 : ∀ x : ℝ, f (x * f (x ^ 2)) = x * f (x ^ 2):= by
            intro x
            specialize h7 x x
            ring_nf at h7
            exact h7
          have h10 : ∀ x y : ℝ, 2 * f (f (x * y)) = x * f y + y * f x:= by
            intro x y
            have h9:= h8 (x + y)
            rw [show (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y by ring_nf] at h9
            have g1:= h6 (x ^ 2 + y ^ 2) (2 * x * y)
            have g2:= h6 (x ^ 2) (y ^ 2)
            rw [←g1, ←g2] at h9
            have g3:= h6 (f (x ^ 2) + f (y ^ 2)) (f (2 * x * y))
            have g4:= h6 (f (x ^ 2)) (f (y ^ 2))
            rw [←g3, ←g4] at h9
            rw [h8 x, h8 y] at h9
            rw [show 2 * x * y = 2 * (x * y) by ring_nf] at h9
            rw [h5 (x * y)] at h9
            rw [h5 (f (x * y))] at h9
            clear g1 g2 g3 g4
            ring_nf at h9
            rw [←(h6 x y)] at h9
            linarith
          have h11 : ∀ x : ℝ, 2 * f (f x) = x + f x:= by
            intro x
            specialize h10 x 1
            rw [h3] at h10
            simp at h10
            exact h10
          have h12 : ∀ x : ℝ, 2 * x * f x = x ^ 2 + f (x ^ 2):= by
            intro x
            specialize h11 (x ^ 2)
            specialize h8 x
            linarith
          have h13 : ∀ x : ℝ, 2 * x * f (x ^ 2) = x ^ 2 * f x + f (x ^ 2) * f x:= by
            intro x
            have h14 : f (f (x * f (x ^ 2))) = x * f (x ^ 2):= by
              rw [h9 x]
              rw [h9 x]
            have h15:= h10 x (f (x ^ 2))
            rw [show 2 * x * f (x ^ 2) = 2 * (x * f (x ^ 2)) by ring_nf]
            rw [←h14, h15, h8 x]
            linarith
          -- Final steps to prove f(x) = x
          have h14 : ∀ x : ℝ, 2 * x * (x - f x) ^ 2 = 0:= by
            intro x
            specialize h13 x
            specialize h12 x
            replace h12 : f (x ^ 2) = 2 * x * f x - x ^ 2:= by linarith
            rw [h12] at h13
            linarith only [h13]
          left
          intro x
          by_cases hx : x = 0
          .
            subst x
            rw [h1]
          .
            specialize h14 x
            replace hx : 2 * x ≠ 0:= by positivity
            replace h14 : (x - f x) ^ 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hx h14
            replace h14 : x - f x = 0:= by exact pow_eq_zero h14
            linarith only [h14]
        -- Case 2: There exists an a where f(a²) = 0
        .
          simp at h2
          rcases h2 with ⟨a, ha, h2⟩
          have h3 : ∀ y : ℝ, f (a * y) = 0:= by
            intro y
            specialize h a y
            simp [hP] at h
            rw [h2] at h
            simp at h
            simp [ha] at h
            exact h
          right
          intro x
          specialize h3 (x / a)
          field_simp at h3
          exact h3
    -- Backward direction: proving that either f(x) = x or f(x) = 0 satisfies the equation
    .
      intro h
      rcases h with h | h
      .
        simp [h]
        intro x y
        ring_nf
      .
        simp [h]
