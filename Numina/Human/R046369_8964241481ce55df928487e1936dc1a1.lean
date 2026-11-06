import Mathlib
/- Man bestimme alle Funktionen $f: \mathbb{R} \rightarrow \mathbb{R}$ mit der Eigenschaft

$$
f(f(x)+y)=2 x+f(f(y)-x)
$$

für alle $x, y \in \mathbb{R}$. -/
theorem algebra_606054 {f : ℝ → ℝ} : (∀ x y, f (f x + y) = 2 * x + f (f y - x)) ↔ ∃ c, ∀ x, f x = x + c:= by
    constructor
    -- Forward direction: proving that if f satisfies the functional equation, then f(x) = x + c
    .
        intro h
        -- First key property: f(y + f(0)) = f(f(y)) for all y
        have h1 : ∀ y : ℝ, f (y + f 0) = f (f y):= by
            intro y
            specialize h 0 y
            simp at h
            rw [show y + f 0 = f 0 + y by ring]
            exact h
        -- Second key property: showing equality of composed functions
        have h2 : ∀ y : ℝ, f (f (f 0 - (f y + (y + f 0)) / 2) + f y) = f (f (f 0 - (f y + (y + f 0)) / 2) + (y + f 0)):= by
            intro y
            set a:= f y with ha
            set b:= y + f 0 with hb
            set m:= f 0 - (a + b) / 2 with hm
            clear_value a b m
            have g1:= h m a
            have g2:= h m b
            specialize h1 y
            rw [←hb, ←ha] at h1
            rw [h1] at g2
            linarith
        -- Third key property: another equality involving composed functions
        have h3 : ∀ y : ℝ, 2 * f y + f (f (f (((f y) + (y + f 0)) / 2)) - f y) = 2 * (y + f 0) + f (f (f (((f y) + (y + f 0)) / 2)) - (y + f 0)):= by
            intro y
            set a:= f y with ha
            set b:= y + f 0 with hb
            set n:= f ((a + b) / 2)
            have g1:= h a n
            have g2:= h b n
            specialize h1 y
            rw [←hb, ←ha] at h1
            rw [h1] at g2
            linarith
        -- Fourth key property: relating function values at midpoints
        have h4 : ∀ y : ℝ, f (f ((f y + (y + f 0)) / 2)) = f y + (y + f 0) + f (f 0 - (f y + (y + f 0)) / 2):= by
            intro y
            set a:= f y
            set b:= y + f 0 with hb
            set m:= f 0 - (a + b) / 2 with hm
            set n:= f ((a + b) / 2) with hn
            have g1:= h ((a + b) / 2) 0
            simp at g1
            rw [←hn, ←hm] at g1
            linarith
        -- Using f(0) as the constant c and proving f(x) = x + c
        use (f 0)
        intro y
        specialize h2 y
        specialize h3 y
        specialize h4 y
        set a:= f y with ha
        set b:= y + f 0 with hb
        set m:= f 0 - (a + b) / 2 with hm
        set n:= f ((a + b) / 2) with hn
        clear_value a b m n
        replace h4 : f n - a = f m + b:= by linarith
        have h5 : f n - b = f m + a:= by linarith
        rw [h4, h5, h2] at h3
        linarith
    -- Backward direction: proving that if f(x) = x + c, then it satisfies the functional equation
    .
        intro h
        rcases h with ⟨c, hc⟩
        simp [hc]
        intro x y
        linarith
