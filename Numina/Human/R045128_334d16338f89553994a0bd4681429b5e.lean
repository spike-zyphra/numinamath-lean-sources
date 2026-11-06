import Mathlib

/- If $|z| = 1$, express $\overline{z}$ as a simplified fraction in terms of $z$. -/
theorem algebra_20567 {z : ℂ} (hz : ‖z‖ = 1) :
    (starRingEnd ℂ) z = 1 / z := by
    -- simplify the expression
    simp at hz
    -- only need to prove \overline{z} * z = 1
    suffices (starRingEnd ℂ) z * z = ↑1 by exact eq_one_div_of_mul_eq_one_left this
    -- use the fact that |z|² = z * \overline{z}
    rw [←Complex.normSq_eq_conj_mul_self, ←Complex.mul_self_abs, hz]
    -- trivial calculation
    field_simp
