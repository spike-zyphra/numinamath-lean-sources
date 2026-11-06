import Mathlib
/- Trouver toutes les fonctions $f: \mathbb{R} \rightarrow \mathbb{R}$ telles que

$$
f(x+f(y))+x=f(f(2 x)+y)
$$

pour tous les réels $x$ et $y$. -/
theorem algebra_606164 (f : ℝ → ℝ) :
    (∀ x y, f (x + f y) + x = f (f (2 * x) + y)) ↔ ∃ a, ∀ x, f x = x + a := by
    constructor
    -- Forward direction: proving that if f satisfies the functional equation, then f(x) = x + a for some constant a
    .
        set P : ℝ × ℝ → Prop := fun (x, y) => f (x + f y) + x = f (f (2 * x) + y) with hP
        -- Define a as f(0), this will be our constant
        set a:= f 0 with ha
        clear_value P a
        intro h
        -- Rewrite the hypothesis using P
        replace h : ∀ x y, P (x, y) := by
            intro x y
            rw [hP]
            exact h x y
        -- Key equation relating f(2x + a) and f(x + a)
        have h1 : ∀ x : ℝ, f (2 * x + a) = f (x + a) + x := by
            intro x
            have g1:= h x 0
            have g2:= h 0 (2 * x)
            simp [hP] at g1 g2
            rw [←ha] at g1 g2
            rw [show a + 2 * x = 2 * x + a by ring_nf] at g2
            linarith
        -- Prove that f(-a) = 0
        have h2 : f (-a) = 0:= by
            specialize h1 (-a)
            ring_nf at h1
            rw [←ha] at h1
            linarith
        -- Prove that f is surjective
        have h3 : ∀ x : ℝ, ∃ z : ℝ, f z = x := by
            intro x
            set y:= -f (-2 * x) - a with hy
            set z:= -x + f y with hz
            clear_value y z
            specialize h (-x) y
            simp [hP] at h
            rw [←hz, hy] at h
            ring_nf at h
            rw [h2] at h
            use z
            linarith
        -- Prove that f is injective
        have h4 : ∀ x y : ℝ, f x = f y → x = y := by
            intro x y hxy
            set d:= y - x with hd
            clear_value d
            -- Show that f(t+x) = f(t+y) for all t
            have h4 : ∀ t : ℝ, f (t + x) = f (t + y) := by
                intro t
                specialize h3 t
                rcases h3 with ⟨z, hz⟩
                have g1 := h (z / 2) x
                have g2 := h (z / 2) y
                simp [hP] at g1 g2
                ring_nf at g1 g2
                rw [hz] at g1 g2
                rw [hxy] at g1
                rw [←g1, ←g2]
            -- Use previous result to show f(2x) = f(2y)
            have h5 : f (x * 2) = f (y * 2) := by
                have g1 := h4 x
                have g2 := h4 y
                ring_nf at g1 g2
                rw [g1, g2]
            -- Show that f(x+a) = f(y+a)
            have h6 : f (x + a) = f (y + a) := by
                specialize h4 a
                rw [show x + a = a + x by ring_nf, show y + a = a + y by ring_nf]
                exact h4
            have g1 := h x 0
            have g2 := h y 0
            simp [hP] at g1 g2
            rw [←ha] at g1 g2
            rw [show 2 * x = x * 2 by ring_nf] at g1
            rw [show 2 * y = y * 2 by ring_nf] at g2
            rw [h5, h6] at g1
            linarith
        use a
        intro x
        specialize h 0 x
        simp [hP] at h
        specialize h4 (f x) (f 0 + x) h
        rw [←ha] at h4
        linarith
    -- Backward direction: proving that if f(x) = x + a, then it satisfies the functional equation
    .
        intro h
        rcases h with ⟨a, h⟩
        simp [h]
        intro x y
        linarith
