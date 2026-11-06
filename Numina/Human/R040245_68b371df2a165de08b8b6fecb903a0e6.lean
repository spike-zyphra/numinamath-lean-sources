import Mathlib

/- Show that in the expressions


$$

4 t, \quad 3-2 t-t^{2}, \quad 3+2 t-t^{2}

$$


substituting integers for $t$ always results in a triplet of numbers whose sum of squares is twice a square number, and whose fourth power sum is twice a fourth power. -/
theorem algebra_175467 (t : ℤ) :
    (∃ n, (4*t)^2 + (3-2*t-t^2)^2 + (3+2*t-t^2)^2 = 2*n^2) ∧
    ∃ m, (4*t)^4 + (3-2*t-t^2)^4 + (3+2*t-t^2)^4 = 2*m^4 := by

    constructor

    --We have the identity 4*t)^2 + (3-2*t-t^2)^2 + (3+2*t-t^2)^2 = 2 * (3 + t^2)^2.
    have h1 : (4*t)^2 + (3-2*t-t^2)^2 + (3+2*t-t^2)^2 = 2 * (3 + t^2)^2 := by ring
    --Use 3 + t^2 as the witness
    use (3 + t^2)
    ring_nf

    --We have the identity (4*t)^4 + (3-2*t-t^2)^4 + (3+2*t-t^2)^4 = 2 * (3 + t^2)^4.
    have h2 : (4*t)^4 + (3-2*t-t^2)^4 + (3+2*t-t^2)^4 = 2 * (3 + t^2)^4 := by ring
    --Use 3 + t^2 as the witness.
    use (3 + t^2)
    ring