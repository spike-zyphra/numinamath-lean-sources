import Mathlib
/- Find all functions $\mathrm{f}: \mathbb{R} \longrightarrow \mathbb{R}$ such that for all $x, y$ in $\mathbb{R}$,

$$
f(x+y)^{2}-f\left(2 x^{2}\right)=f(y+x) f(y-x)+2 x f(y)
$$ -/
theorem algebra_607711 (f : ℝ → ℝ) : (∀ x y, f (x + y) ^ 2 - f (2 * x ^ 2) = f (y + x) * f (y - x) + 2 * x * f y) ↔
(∀ x, f x = 0) ∨ (∀ x, f x = x) := by
    constructor
    -- Forward direction: proving that f must be either identically 0 or the identity function
    .
        intro h
        -- First, prove that f(0) = 0 by setting x = y = 0 in the original equation
        have h1 : f 0 = 0:= by
            specialize h 0 0
            simp at h
            linarith
        -- Prove that f(x)² = f(-x)² for all x
        have h2 : ∀ x : ℝ, (f x) ^ 2 = (f (-x)) ^ 2:= by
            intro x
            have g1:= h x 0
            have g2:= h (-x) 0
            simp at g1 g2
            rw [h1] at g1 g2
            simp at g1 g2
            linarith
        -- Prove that x·f(y) = y·f(x) for all x,y
        have h3 : ∀ x y : ℝ, x * f y = y * f x:= by
            intro x y
            have g1:= h (-x) y
            have g2:= h x y
            ring_nf at g1 g2
            have g3 : (f (x + y)) ^ 2 - (f (-x + y)) ^ 2 =  4 * x * f y:= by linarith
            clear g1 g2
            have g1:= h (-y) x
            have g2:= h y x
            ring_nf at g1 g2
            have g4 : (f (y + x)) ^ 2 - (f (-y + x)) ^ 2 = 4 * y * f x:= by linarith
            clear g1 g2
            specialize h2 (-x + y)
            rw [show -(-x + y) = -y + x by ring] at h2
            rw [show x + y = y + x by ring] at g3
            linarith
        -- Show f must be linear: f(x) = ax for some constant a
        have h4 : ∃ a : ℝ, ∀ x : ℝ, f x = a * x:= by
            use (f 1)
            intro x
            specialize h3 x 1
            simp at h3
            linarith
        rcases h4 with ⟨a, h4⟩
        simp [h4] at h
        have g1:= h 1 0
        ring_nf at g1
        -- Show that a must be either 0 or 1
        replace g1 : a * (a - 1) = 0:= by linarith
        replace g1 : a = 0 ∨ a - 1 = 0:= by exact mul_eq_zero.mp g1
        rcases g1 with g1 | g1
        -- Case a = 0: f is identically 0
        .
            subst a
            simp [h4]
        -- Case a = 1: f is the identity function
        .
            replace g1 : a = 1:= by linarith
            subst a
            simp [h4]
    -- Backward direction: verify that both f = 0 and f(x) = x satisfy the original equation
    .
        intro h
        rcases h with h | h
        -- Verify the case where f = 0
        .
            simp [h]
        -- Verify the case where f(x) = x
        .
            simp [h]
            intro x y
            ring_nf
