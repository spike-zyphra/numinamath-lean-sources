import Mathlib

/- For $y=\frac{x-4}{5x-10}$ and $x\neq 2$, what is the value of $y$ that is not attainable? Express your answer as a common fraction. -/
theorem algebra_20097 (y : ℝ) : (∀ x : ℝ, x ≠ 2 -> y ≠ (x - 4) / (5 * x - 10)) -> y = 1 / 5:= by
    -- Assume by contradiction that there exists a y value that cannot be attained
    intro h
    by_contra H

    -- Consider a specific x value: x = (10y - 4)/(5y - 1)
    -- First prove that this x is not equal to 2
    have h1 : (10 * y - 4) / (5 * y - 1) ≠ 2:= by
        by_contra H1
        -- If y = 1/5, then 5y - 1 = 0, which would make the fraction undefined
        replace H : 5 * y - 1 ≠ 0:= by
            by_contra H2
            replace H2 : y = 1 / 5:= by linarith
            trivial
        field_simp at H1
        linarith

    -- Apply the hypothesis to our chosen x value
    specialize h ((10 * y - 4) / (5 * y - 1)) h1

    -- Show that plugging this x back into the original function gives us y
    -- This contradicts our assumption that y is unattainable
    have h2 :  y = ((10 * y - 4) / (5 * y - 1) - 4) / (5 * ((10 * y - 4) / (5 * y - 1)) - 10):= by
        replace H : 5 * y - 1 ≠ 0:= by
            by_contra H2
            replace H2 : y = 1 / 5:= by linarith
            trivial
        field_simp
        ring_nf
    trivial
