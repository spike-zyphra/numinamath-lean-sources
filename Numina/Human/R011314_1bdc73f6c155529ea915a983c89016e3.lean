import Mathlib

open Real Set
open Complex(I)

/- 9. Let the complex number $z=3 \cos \theta+\mathrm{i} \cdot 2 \sin \theta$, find the maximum value of the function $y=\theta-\arg z\left(0<\theta<\frac{\pi}{2}\right)$ and the corresponding $\theta$ value. -/
theorem algebra_107261 :
    IsGreatest {θ - (Complex.arg (3 * cos θ + I * 2 * sin θ)) | (θ : ℝ) (_ : θ ∈ Set.Ioo 0 (π / 2))}
    (arctan (1 / (2 * √6))) := by
  constructor
  -- first we'll show using arctan(√6/2) we get the exact value
  . simp
    use arctan (√6 / 2)
    and_intros
    -- showing that the witness is within (0, π / 2) is easy
    . rw [← arctan_zero]
      apply arctan_lt_arctan
      positivity
    . apply arctan_lt_pi_div_two
    -- to show ti does produce arctan (1 / (2 * √6)), first convert goals to real cos, sin
    . rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_arctan, sin_arctan]
      -- simplify and write the arg as sin, then simplify the abs
      ring_nf; simp; ring_nf
      simp [Complex.arg]
      have ht : ↑√2 / ↑√5 * 3 + ↑√2 / ↑√5 * I * ↑√6 = ↑(√2 / √5 * 3 : ℝ) + ↑(√2 / √5 * √6 : ℝ) * I := by
        push_cast
        ring
      rw [ht, Complex.abs_add_mul_I]
      ring_nf; simp; ring_nf
      rw [show √6 * √2 * (√5)⁻¹ * (√6)⁻¹ = √2 / √5 by field_simp; ring]
      -- now target is arctan _ - arcsin _ = arctan _, convert the arctsin to arctan
      replace ht := arctan_eq_arcsin (√2/√3)
      ring_nf at ht; simp at ht; ring_nf at ht; simp at ht
      rw [show √2 * (√3)⁻¹ * (√3 / √5) = √2 / √5 by field_simp] at ht
      rw [← ht]
      -- convert the subtraction to addition as mathlib as addition formula for arctan which works if arguments multiply to be less than 1
      change arctan (√6 * (1 / 2)) + - arctan (√2 * (√3)⁻¹) = arctan ((√6)⁻¹ * (1 / 2))
      rw [← arctan_neg, arctan_add]
      swap
      . suffices 0 < -(√6 * (1 / 2) * -(√2 * (√3)⁻¹)) by linarith
        simp
      congr
      -- now we simplify the expressions inside arctan and get equality
      field_simp
      ring_nf
      simp
      rw [show (6 : ℝ) = 2 * 3 by norm_num]
      rw [sqrt_mul (by positivity)]
      ring_nf
      simp
      linarith
  -- to prove it's an upper bound, first get bounds on θ, and a = the arg expressino
  . rintro y ⟨θ, hθ, hy⟩
    obtain ⟨hθ_lb, hθ_ub⟩ := hθ
    let a := (3 * ↑(cos θ) + I * 2 * ↑(sin θ)).arg
    have ha_lb : 0 ≤ a := by
      rw [Complex.arg_nonneg_iff]
      simp
      norm_cast
      apply sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have : 0 < cos θ := by
      apply cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have ha_ub : a < π / 2 := by
      rw [Complex.arg_lt_pi_div_two_iff]
      left
      simp
      norm_cast
    rw [← hy]
    -- change the goal to arctan _ + arctan _ ≤ arctan _, then we can use addition formula
    change θ + - a ≤ arctan (1 / (2 * √6))
    rw [← arctan_tan (x := θ) (by linarith) (by linarith)]
    rw [← arctan_tan (x := a) (by linarith) (by linarith)]
    rw [← arctan_neg]
    have ht : tan θ * (- tan a) < 1 := by
      suffices 0 ≤ tan θ * tan a by linarith
      apply mul_nonneg <;> apply tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
    rw [arctan_add ht]
    -- now using monotonicity of arctan our goal is to only work with tans
    apply arctan_le_arctan
    -- convert tan a in terms of tan θ
    replace ht : tan a = 2 / 3 * tan θ := by
      simp [a]
      norm_cast
      rw [tan_eq_sin_div_cos]
      field_simp
    rw [ht]
    have : 0 < tan θ := by
      apply tan_pos_of_pos_of_lt_pi_div_two <;> linarith
    -- change the expression to be constant / (3 / tan θ + 2 * tan θ), we can use am-gm on denominator
    replace ht : (tan θ + -(2 / 3 * tan θ)) / (1 - tan θ * -(2 / 3 * tan θ)) = 1 / (3 / tan θ + 2 * tan θ) := by
      field_simp
      ring
    rw [ht]
    -- convert the goal to denominators of target and current expression and use am-gm
    gcongr
    convert two_mul_le_add_sq (√(3 / tan θ)) (√(2 * tan θ)) using 1
    . rw [mul_assoc, ← sqrt_mul (by positivity), show (6 : ℝ) = 2 * 3 by norm_num]
      rw [sqrt_mul (by positivity)]
      field_simp
      ring
    . rw [sq_sqrt (by positivity), sq_sqrt (by positivity)]