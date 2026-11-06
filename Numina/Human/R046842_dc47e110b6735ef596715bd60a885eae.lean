import Mathlib
/- Let $f$ be a bounded real function defined for all real numbers and satisfying for all real numbers $x$ the condition

$$
f\left(x+\frac{1}{3}\right)+f\left(x+\frac{1}{2}\right)=f(x)+f\left(x+\frac{5}{6}\right)
$$

Show that $f$ is periodic. (A function $f$ is bounded, if there exists a number $L$ such that $|f(x)|< L $ for all real numbers $x$. A function $f$ is periodic, if there exists a positive number $k$ such that $f(x+k)=f(x)$ for all real numbers $x$.) -/

theorem algebra_607973 {f : ℝ → ℝ} (h : ∃ L, ∀ x, |f x| < L)
    (h1 : ∀ x, f (x + 1 / 3) + f (x + 1 / 2) = f x + f (x + 5 / 6)) :
    ∃ k, 0 < k ∧ Function.Periodic f k := by
        -- Extract the bound L from hypothesis
        rcases h with ⟨L, hL⟩
        -- Define auxiliary function g(x) = f(x/6) to simplify calculations
        set g : ℝ → ℝ:= fun x => f (x / 6) with hg
        clear_value g
        -- Show that g is also bounded by L
        have hgL : ∀ x, |g x| < L:= by
            simp [hg]
            intro x
            specialize hL (x / 6)
            exact hL
        -- Transform the functional equation in terms of g
        -- g(t+2) + g(t+3) = g(t) + g(t+5)
        have h2 : ∀ t : ℝ, g (t + 2) + g (t + 3) = g t + g (t + 5):= by
            intro t
            simp [hg]
            specialize h1 (t / 6)
            ring_nf at h1
            ring_nf
            exact h1
        -- Prove that differences over length 6 intervals are equal
        -- g(t+12) - g(t+6) = g(t+6) - g(t)
        have h3 : ∀ t : ℝ, g (t + 12) - g (t + 6) = g (t + 6) - g t:= by
            intro t
            have g1 := h2 (t + 7)
            have g2 := h2 (t + 5)
            have g3 := h2 (t + 3)
            have g4 := h2 (t + 4)
            have g5 := h2 (t + 2)
            have g6 := h2 t
            ring_nf at g1 g2 g3 g4 g5 g6
            ring_nf
            linarith
        -- Prove that the difference over any number of 6-unit intervals is constant
        have h4 : ∀ n : ℕ, ∀ t : ℝ, (g (t + 6 * n + 6) - g (t + 6 * n)) = (g (t + 6) - g t):= by
            intro n
            induction n with
            | zero =>
                intro t
                simp
            | succ n ih =>
                intro t
                simp
                specialize ih t
                specialize h3 (t + 6 * n)
                ring_nf at h3 ih
                ring_nf
                linarith
        -- Show that the difference over n intervals is n times the difference over one interval
        have h5 : ∀ n : ℕ, ∀ t : ℝ, (g (t + 6 * n) - g t) = n * (g (t + 6) - g t):= by
            intro n
            induction n with
            | zero =>
                intro t
                simp
            | succ n ih =>
                intro t
                simp
                specialize ih t
                specialize h4 n t
                ring_nf at ih h4
                ring_nf
                linarith
        -- Show that L is positive
        have hLpos : L > 0:= by
            specialize hL 0
            have hf0 : |f 0| ≥ 0:= by positivity
            linarith
        -- Prove that g(t+6) - g(t) = 0 using boundedness
        have h6 : ∀ t : ℝ, g (t + 6) - g t = 0:= by
            intro t
            by_contra H
            replace H : |g (t + 6) - g t| > 0:= by positivity
            set e:= |g (t + 6) - g t| with he
            clear_value e
            have h6 : ∀ n : ℕ, |g (t + 6 * n) - g t| ≤ 2 * L:= by
                intro n
                have g1:= hgL (t + 6 * n)
                have g2:= hgL t
                have g3 : |g (t + 6 * n) - g t| ≤ |g (t + 6 * n)| + |g t|:= by exact abs_sub (g (t + 6 * ↑n)) (g t)
                linarith
            specialize h6 (1 + ⌊(2 * L) / e⌋.natAbs)
            specialize h5 (1 + ⌊(2 * L) / e⌋.natAbs) t
            rw [h5] at h6
            clear h5
            have h7 : (2 * L) / e ≥ 0:= by positivity
            replace h7 : ⌊(2 * L) / e⌋ ≥ 0:= by exact Int.floor_nonneg.mpr h7
            simp at h6
            have h8 : (↑⌊(2 * L) / e⌋.natAbs : ℝ) = (↑(↑⌊(2 * L) / e⌋.natAbs : ℤ) : ℝ):= by rfl
            rw [h8] at h6
            simp at h6
            have h9 : |(↑⌊(2 * L) / e⌋ : ℝ)| = ⌊(2 * L) / e⌋:= by
                rify at h7
                exact abs_of_nonneg h7
            rw [h9] at h6
            rw [show |(1 + ↑⌊(2 * L) / e⌋) * (g (t + 6) - g t)| = |1 + ↑⌊(2 * L) / e⌋| * |g (t + 6) - g t| by exact abs_mul (1 + ↑⌊(2 * L) / e⌋ : ℝ) (g (t + 6) - g t)] at h6
            rw [←he] at h6
            rw [show |1 + (↑⌊(2 * L) / e⌋ : ℝ)| = 1 + ↑⌊(2 * L) / e⌋ by exact abs_of_nonneg (by positivity)] at h6
            replace h9 : ↑⌊(2 * L) / e⌋ > (2 * L) / e - 1:= by exact Int.sub_one_lt_floor (2 * L / e)
            replace h9 : 1 + ↑⌊(2 * L) / e⌋ > 2 * L / e:= by linarith
            replace h9 : (1 + ↑⌊(2 * L) / e⌋) * e > (2 * L / e) * e:= by exact mul_lt_mul_of_pos_right h9 (by positivity)
            rw [show (2 * L / e) * e = 2 * L by field_simp] at h9
            linarith
        -- Finally, prove that f is periodic with period 1
        use 1
        simp
        intro x
        specialize h6 (6 * x)
        simp [hg] at h6
        ring_nf at h6
        ring_nf
        linarith
