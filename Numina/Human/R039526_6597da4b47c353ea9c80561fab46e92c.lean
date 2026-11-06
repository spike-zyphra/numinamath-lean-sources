import Mathlib
/- Find all triples $(x, y, z)$ of real numbers that satisfy the system

$$
\left\{\begin{array}{l}
x+y+z=2008 \\
x^{2}+y^{2}+z^{2}=6024^{2} \\
\frac{1}{x}+\frac{1}{y}+\frac{1}{z}=\frac{1}{2008}
\end{array}\right.
$$ -/
theorem algebra_604671 : {(x, y, z) : ℝ × ℝ × ℝ | x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x + y + z = 2008 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 6024 ^ 2 ∧ 1 / x + 1 / y + 1 / z = 1 / 2008} = {(2008, 4016, -4016), (2008, -4016, 4016), (4016, 2008, -4016), (4016, -4016, 2008), (-4016, 2008, 4016), (-4016, 4016, 2008)}:= by
    -- Use extensionality to prove set equality
    ext ⟨x, y, z⟩
    constructor
    .
        intro h
        simp at h
        rcases h with ⟨hx, hy, hz, h1, h2, h3⟩
        -- Simplify the fraction equation to standard form
        replace h3 : 1 / x + 1 / y + 1 / z = 1 / 2008:= by simp [h3]
        -- Clear denominators in the fraction equation
        field_simp at h3
        -- Transform equation to a more useful form
        replace h3 : x * y * z = 2008 * (x * y + y * z + z * x):= by linarith
        -- Key insight: rearrange to get a factored form
        have h4 : (x - 2008) * ((y - 2008) * (z - 2008))= 0:= by linarith
        -- Apply zero product property
        replace h4 : x - 2008 = 0 ∨ (y - 2008) * (z - 2008) = 0:= by exact mul_eq_zero.mp h4

        -- Helper lemma: if any variable equals 2008, the other two must be 4016 and -4016
        have h5 : ∀ x y z : ℝ, x + y + z = 2008 → x ^ 2 + y ^ 2 + z ^ 2 = 6024 ^ 2 → x * y * z =
         2008 * (x * y + y * z + z * x) → x = 2008 → (y = 4016 ∧ z = -4016 ∨ y = -4016 ∧ z = 4016):= by
            intro x y z h1 h2 h3 h4
            subst x
            -- When x = 2008, y and z must sum to 0
            replace h1 : y = -z:= by linarith
            rw [h1] at h2
            simp at h2
            -- Solve the resulting quadratic equation
            replace h2 : (z - 4016) * (z + 4016) = 0:= by linarith
            replace h2 : z - 4016 = 0 ∨ z + 4016 = 0:= by exact mul_eq_zero.mp h2
            rcases h2 with h2 | h2
            .
                replace h2 : z = 4016:= by linarith
                subst z y
                simp
            .
                replace h2 : z = -4016:= by linarith
                subst z y
                simp
        -- Main proof: handle all possible cases
        rcases h4 with h4 | h4
        -- Case 1: When x = 2008
        .
            replace h4 : x = 2008:= by linarith
            specialize h5 x y z h1 h2 h3 h4
            rcases h5 with h5 | h5
            all_goals
            rcases h5 with ⟨h5, h6⟩
            subst x y z
            simp
        -- Case 2: When either y = 2008 or z = 2008
        .
            replace h4 : y - 2008 = 0 ∨ z - 2008 = 0:= by exact mul_eq_zero.mp h4
            rcases h4 with h4 | h4
            -- Case 2a: When y = 2008
            .
                replace h4 : y = 2008:= by linarith
                specialize h5 y x z (by linarith only [h1]) (by linarith only [h2]) (by linarith only [h3]) h4
                rcases h5 with h5 | h5
                all_goals
                rcases h5 with ⟨h5, h6⟩
                subst y x z
                simp
            -- Case 2b: When z = 2008
            .
                replace h4 : z = 2008:= by linarith
                specialize h5 z x y (by linarith only [h1]) (by linarith only [h2]) (by linarith only [h3]) h4
                rcases h5 with h5 | h5
                all_goals
                rcases h5 with ⟨h5, h6⟩
                subst z y x
                simp
    .
        -- Prove the reverse direction: all six triples satisfy the equations
        intro h
        simp at h
        rcases h with h | h | h | h | h | h
        all_goals
        rcases h with ⟨h1, h2, h3⟩
        subst x y z
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals
            ring_nf
        all_goals
            simp
