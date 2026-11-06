import Mathlib
/- Find all functions $f$ defined on all real numbers and taking real values such that

$$
f(f(y))+f(x-y)=f(x f(y)-x)
$$

for all real numbers $x, y$.

Answer: $f(x)=0$. -/
theorem algebra_238086 {f : ℝ → ℝ} : ( ∀ x y, f (f y) + f (x - y) = f (x * f y - x)) ↔
∀ x, f x = 0:= by
  constructor
  -- Forward direction: proving that the functional equation implies f(x) = 0
  .
    intro h
    -- First prove that f(f(0)) = 0 by setting x = y = 0
    have h1 : f (f 0) = 0:= by
        specialize h 0 0
        simp at h
        exact h
    -- Then prove that f(0) = 0 using x = f(0)/2 and y = f(0)
    replace h1 : f 0 = 0:= by
        specialize h (f 0 / 2) (f 0)
        rw [h1] at h
        ring_nf at h
        linarith
    -- Prove that f is an even function: f(x) = f(-x)
    have h2 : ∀ x : ℝ, f x = f (-x):= by
        intro x
        specialize h x 0
        rw [h1] at h
        rw [h1] at h
        ring_nf at h
        exact h
    -- Prove that f(f(y)) = -f(y) for all y
    have h3 : ∀ y : ℝ, f (f y) = -f y:= by
        intro y
        specialize h 0 y
        ring_nf at h
        rw [h1] at h
        rw [←h2 y] at h
        linarith
    -- Finally prove that f(y) = 0 for all y using previous results
    intro y
    have g1:= h3 y
    have g2:= h3 (f y)
    rw [g1] at g2
    rw [←h2 (f y)] at g2
    simp at g2
    linarith
  -- Backward direction: proving that if f(x) = 0, then the functional equation holds
  .
    intro h
    simp [h]
