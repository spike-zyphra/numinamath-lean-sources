import Mathlib
/- Find all triples $(x, y, z)$ of positive integers satisfying the system of equations

$$
\left\{\begin{array}{l}
x^{2}=2(y+z) \\
x^{6}=y^{6}+z^{6}+31\left(y^{2}+z^{2}\right)
\end{array}\right.
$$ -/
theorem algebra_241477 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x ^ 2 = 2 * (y + z) ∧ x ^ 6 = y ^ 6 + z ^ 6 + 31 * (y ^ 2 + z ^ 2)} = {(2, 1, 1)}:= by
    -- Use extensionality to prove set equality
    ext ⟨x, y, z⟩
    constructor
    -- Forward direction: if (x,y,z) is a solution, then it must be (2,1,1)
    .
        intro h
        simp at h
        rcases h with ⟨hx, hy, hz, h1, h2⟩
        -- From x^2 = 2(y+z), we know 2 divides x^2
        have h3 : 2 ∣ x ^ 2:= by exact Dvd.intro (y + z) (id (Eq.symm h1))
        -- 2 is prime
        have h4 : Nat.Prime 2:= by norm_num
        -- If 2 divides x^2, then 2 divides x (since 2 is prime)
        replace h3 : 2 ∣ x:= by exact Nat.Prime.dvd_of_dvd_pow h4 h3
        -- Both terms on RHS of second equation are positive
        have h5 : z ^ 6 + 31 * (y ^ 2 + z ^ 2)> 0:= by positivity
        have h6 : y ^ 6 + 31 * (y ^ 2 + z ^ 2)> 0:= by positivity
        -- Therefore x^6 > y^6 and x^6 > z^6
        replace h5 : x ^ 6 > y ^ 6:= by linarith
        replace h6 : x ^ 6 > z ^ 6:= by linarith
        -- Which means x > y and x > z
        replace h5 : x > y:= by exact lt_of_pow_lt_pow_left' 6 h5
        replace h6 : x > z:= by exact lt_of_pow_lt_pow_left' 6 h6
        -- From first equation: 4x > x^2
        have h7 : 4 * x > x * x:= by linarith
        -- Therefore 4 > x
        replace h7 : 4 > x:= by exact (Nat.mul_lt_mul_right hx).mp h7
        -- Since 2|x, x = 2x₁ for some x₁
        replace h3 : ∃ x1 : ℕ, x = 2 * x1:= by exact h3
        rcases h3 with ⟨x1, hx1⟩
        rw [hx1] at hx h7
        simp at hx
        -- From 4 > 2x₁, we get x₁ < 2
        replace h7 : x1 < 2:= by linarith
        -- Since x₁ is positive, x₁ = 1
        replace h7 : x1 = 1:= by linarith
        subst x1
        simp at hx1
        subst x
        -- From first equation: y + z = 2
        replace h1 : y + z = 2:= by linarith
        -- Since y,z are positive and y + z = 2, y = z = 1
        replace h5 : y = 1:= by linarith
        replace h6 : z = 1:= by linarith
        subst y z
        simp
    -- Backward direction: verify that (2,1,1) is indeed a solution
    .
        intro h
        simp at h
        rcases h with ⟨h1, h2, h3⟩
        subst x y z
        simp