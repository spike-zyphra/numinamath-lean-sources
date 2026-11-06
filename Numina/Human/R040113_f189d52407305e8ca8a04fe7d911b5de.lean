import Mathlib
/- Bepaal alle drietallen $(x, y, z)$ van niet-negatieve reële getallen die voldoen aan het stelsel vergelijkingen

$$
\begin{aligned}
& x^{2}-y=(z-1)^{2} \\
& y^{2}-z=(x-1)^{2} \\
& z^{2}-x=(y-1)^{2}
\end{aligned}
$$ -/
theorem algebra_605741 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : x ^ 2 - y = (z - 1) ^ 2) (h2 : y ^ 2 - z = (x - 1) ^ 2) (h3 : z ^ 2 - x = (y - 1) ^ 2) :
    (x, y, z) = (1, 1, 1) := by
        -- Helper lemma g1: Proves that if x is the minimum among x,y,z, then x=y=z=1
        have g1 : ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → (x ≤ y ∧ x ≤ z) → x ^ 2 - y = (z - 1) ^ 2 → y ^ 2 - z = (x - 1) ^ 2 → z ^ 2 - x = (y - 1) ^ 2 → x = 1 ∧ y = 1 ∧ z = 1:= by
            intro x y z hx hy hz h h1 h2 h3
            -- Sum of x, y, z equals 3
            have h4 : x + y + z = 3 := by linarith
            rcases h with ⟨g1, g2⟩
            -- For x ≤ 1, we have x² ≤ x
            have g4 : x ^ 2 ≤ x:= by
                replace g3 : 1 - x ≥ 0:= by linarith
                replace g3 : x * (1 - x) ≥ 0:= by positivity
                linarith only [g3]
            -- Square of z-1 is non-negative
            have g5 : (z - 1) ^ 2 ≥ 0:= by positivity
            -- x(x-1) = 0, so x = 0 or x = 1
            replace g4 : x * (x - 1) = 0:= by linarith
            replace g3 : x = y:= by linarith
            replace g4 : x = 0 ∨ x - 1 = 0:= by exact mul_eq_zero.mp g4
            rcases g4 with g4 | g4
            . -- Case x = 0 leads to contradiction
                subst x y
                simp at h4
                subst z
                by_contra _
                ring_nf at h1
                linarith
            . -- Case x = 1 gives the solution
                replace g4 : x = 1:= by linarith
                subst x y
                replace h4 : z = 1:= by linarith
                subst z
                simp

        -- Proves that one of x,y,z must be minimum among the three
        have g2 : (x ≤ y ∧ x ≤ z) ∨ (y ≤ z ∧ y ≤ x) ∨ (z ≤ x ∧ z ≤ y):= by
            by_contra H
            simp at H
            rcases H with ⟨H1, H2, H3⟩
            -- At least one inequality must hold
            have H4 : x ≤ y ∨ y ≤ z ∨ z ≤ x:= by
                by_contra M
                simp at M
                rcases M with ⟨M1, M2, M3⟩
                linarith
            rcases H4 with H4 | H4 | H4
            . -- Case x ≤ y leads to contradiction
                replace H1:= H1 H4
                replace H3:= H3 (by linarith)
                linarith
            . -- Case y ≤ z leads to contradiction
                replace H2:= H2 H4
                replace H1:= H1 (by linarith)
                linarith
            . -- Case z ≤ x leads to contradiction
                replace H3:= H3 H4
                replace H2:= H2 (by linarith)
                linarith

        -- Apply g1 to each case where x, y, or z is minimum
        rcases g2 with g2 | g2 | g2
        . -- Case where x is minimum
            specialize g1 x y z hx hy hz g2 h1 h2 h3
            rcases g1 with ⟨gx, gy, gz⟩
            subst x y z
            simp
        . -- Case where y is minimum
            specialize g1 y z x hy hz hx g2 (by linarith) (by linarith) (by linarith)
            rcases g1 with ⟨gy, gz, gx⟩
            subst y z x
            simp
        . -- Case where z is minimum
            specialize g1 z x y hz hx hy g2 (by linarith) (by linarith) (by linarith)
            rcases g1 with ⟨gz, gx, gy⟩
            subst z x y
            simp
