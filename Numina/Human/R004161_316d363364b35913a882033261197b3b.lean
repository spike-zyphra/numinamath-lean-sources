import Mathlib
/- The real-valued function $f$ is defined for all positive integers. For any integers $a>1, b>1$ with $d=\operatorname{gcd}(a, b)$, we have

$$
f(a b)=f(d) \cdot\left(f\left(\frac{a}{d}\right)+f\left(\frac{b}{d}\right)\right),
$$

Determine all possible values of $f(2001)$. -/
theorem number_theory_240211 : {S : ℝ | ∃ f : ℕ → ℝ, (∀ a b, 1 < a → 1 < b → f (a * b) = f (Nat.gcd a b) * (f (a / Nat.gcd a b) + f (b / Nat.gcd a b))) ∧ S = f 2001} = {0, 1 / 2}:= by
    -- We prove equality of sets by showing each is a subset of the other
    ext S
    constructor
    .
        -- First direction: if S is in the set of possible values of f(2001), then S is either 0 or 1/2
        intro h
        simp at h
        rcases h with ⟨f, hf, hS⟩
        subst S
        -- Proof by contradiction: assume f(2001) is neither 0 nor 1/2
        by_contra H
        simp at H
        rcases H with ⟨H1, H2⟩
        -- Apply the functional equation to specific values
        -- First with a=3, b=667 (note that 3*667=2001)
        have h1:= hf 3 667 (by omega) (by omega)
        norm_num at h1
        -- Prove that f(1) ≠ 0
        replace h1 : f 1 ≠ 0:= by
            by_contra H
            rw [H] at h1
            simp at h1
            trivial
        -- Apply the functional equation to a=b=2001
        have h2:= hf 2001 2001 (by omega) (by omega)
        norm_num at h2
        -- Apply the functional equation to a=2001, b=2001³
        have h3:= hf 2001 (2001 ^ 3) (by omega) (by omega)
        norm_num at h3
        -- Apply the functional equation to a=b=2001²
        have h4:= hf (2001 ^ 2) (2001 ^ 2) (by omega) (by omega)
        norm_num at h4
        rw [h2] at h4 h3
        -- Derive a constraint equation involving f(1) and f(2001)
        replace h4 : f 1 * f 2001 * (4 * f 1 - 2 * f 2001 - 1) = 0:= by linarith
        simp [H1, h1] at h4
        -- Prove that f(4004001) ≠ 0 (note that 4004001 = 2001²)
        replace h2 : f 4004001 ≠ 0:= by
            by_contra H
            rw [h2] at H
            simp [H1] at H
            trivial
        clear h3
        -- Apply the functional equation to more values
        have h3:= hf (2001 ^ 2) (2001 ^ 2) (by omega) (by omega)
        have h5:= hf (2001 ^ 2) (2001 ^ 6) (by omega) (by omega)
        have h6:= hf (2001 ^ 4) (2001 ^ 4) (by omega) (by omega)
        norm_num at h3 h5 h6
        rw [h3] at h5 h6
        -- Derive another constraint equation
        replace h5 : f 4004001 * f 1 * (4 * f 1 - 2 * f 4004001 - 1) = 0:= by linarith
        simp [h1, h2] at h5
        clear h3 h6
        -- Reapply the functional equation to a=b=2001
        have h3:= hf 2001 2001 (by omega) (by omega)
        norm_num at h3
        -- Derive expressions for f(2001) and f(4004001) in terms of f(1)
        replace h4 : f 2001 = 2 * f 1 - 1 / 2:= by linarith
        replace h5 : f 4004001 = 2 * f 1 - 1 / 2:= by linarith
        rw [h4, h5] at h3
        -- Derive a constraint that forces f(2001) = 1/2
        replace h3 : (2 * f 1 - 1 / 2) * (f 1 - 1 / 2) = 0:= by linarith
        rw [←h4] at h3
        simp [H1] at h3
        field_simp at h3
        replace h4 : f 2001 = 1 / 2:= by linarith
        simp at h4
        trivial
    .
        -- Second direction: prove that both 0 and 1/2 are possible values for f(2001)
        intro h
        simp at h
        rcases h with h | h
        .
            -- Case 1: S = 0
            -- Define f to be the constant zero function
            simp
            use fun _ => 0
            simp
            exact h
        .
            -- Case 2: S = 1/2
            -- Define f to be the constant 1/2 function
            simp
            use fun x => 1 / 2
            simp [h]
            intro a b _ _
            field_simp
