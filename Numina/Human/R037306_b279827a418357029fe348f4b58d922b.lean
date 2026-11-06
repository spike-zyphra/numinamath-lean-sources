import Mathlib

open Complex

/- Find the largest possible real part of
$$
(75+117i)z+\frac{96+144i}{z}
$$
where $z$ is a complex number with $|z|=4$. -/

theorem algebra_93142 (f : ℂ → ℂ) (hf : ∀ z, f z = (75 + 117 * I) * z + (96 + 144 * I) / z) (g : ℂ → Prop) (hg : ∀ z, g z ↔ ‖z‖ = 4) :
IsGreatest {t | ∃ z, g z ∧ (f z).re = t} 540 := by
  -- first convert ‖z‖ = 4 to normSq z = 16, as that format is more useful
  have hz' (z:ℂ) (hz: ‖z‖ = 4) : normSq z = 16 := by
    simp [Complex.abs] at hz
    calc
      normSq z = (√(normSq z))^2 := by
        rw [Real.sq_sqrt]
        exact normSq_nonneg z
      _ = 16 := by rw [hz]; norm_num
  -- for ‖z‖ = 4, the f(z) can be simpliefied to 81a-108b + (126a+69b)i where z = a + bi
  have hf_simp (z : ℂ) (hz: ‖z‖ = 4) : f z = (81 * z.re - 108 * z.im) + (126 * z.re + 69 * z.im) * I := by
    -- first convert the /z into * conj(z) / normSq z
    have hz : normSq z = 16 := by exact hz' z hz
    have hz_nz : z ≠ 0 := by
      refine normSq_pos.mp ?_
      rw [hz]; norm_num
    rw [hf]
    rw [div_eq_mul_inv, Complex.inv_def, hz]
    -- now express z as a + bi
    have : z = z.re + z.im * I := by exact Eq.symm (re_add_im z)
    rw [this] at hz
    simp [Complex.abs, normSq] at hz
    rw [this]; simp [-re_add_im]
    set a := z.re
    set b := z.im
    rw [this] at hz_nz
    -- finally do algebra to prove that f(z) = 81a-108b + (126a+69b)i
    calc
      (75 + 117 * I) * (↑a + ↑b * I) + (96 + 144 * I) * ((↑a + -(↑b * I)) * 16⁻¹) = (75 * a - 117 * b) + (117 * a + 75 * b) * I + (96 + 144 * I) * ((↑a + -(↑b * I)) / 16) := by ring_nf; simp; ring
      _ = (75 * a - 117 * b) + (117 * a + 75 * b) * I + (6 * a + 9 * b) + (9 * a - 6 * b) * I := by ring_nf; simp; ring
      _ = 81 * a - 108 * b + (126 * a + 69 * b) * I := by ring
  -- last fact implies f(z).re = 81a - 108b
  have hf_simp (z : ℂ) (hz: ‖z‖ = 4) : (f z).re = 81 * z.re - 108 * z.im := by
    rw [hf_simp _ hz]
    simp
  -- prove 2 dimensional cauchy schwarz as that'll be used later
  have hcs (a b c d : ℝ) : (a*c + b*d)^2 ≤ (a^2 + b^2) * (c^2 + d^2) := by
    have : 0 ≤ (a * d - b * c) ^ 2 := by exact sq_nonneg _
    ring_nf at this
    ring_nf
    linarith
  -- now prove the target
  constructor
    -- first show that 2.4 - 3.2i = z satisfies condition and then 540 is in target set
  . use (2.4:ℝ) - (3.2:ℝ) * I
    have : ‖(2.4:ℝ) - (3.2:ℝ) * I‖ = 4 := by
      simp [Complex.abs, normSq]
      norm_num
      convert_to √(4^2) = 4
      . congr; norm_num
      . simp
    -- show norm is 4 and f(2.4-3.2i).re = 540
    constructor
    . rw [hg]
      assumption
    . rw [hf_simp _ this]
      simp
      norm_num
    -- now show that 540 is a upper bound, using proven facts rewrite to target 81 * z.re - 108 * z.im ≤ 540
  . rintro t
    rintro ⟨z, hz_norm, hfz⟩
    rw [hg] at hz_norm
    rw [hf_simp _ hz_norm] at hfz
    rw [← hfz]
    have := hz' z hz_norm
    simp [normSq] at this
    ring_nf at this
    -- use cauchy schwarze with 81, -108, z.re, z.im then we get (81 * z.re + -108 * z.im) ^ 2 ≤ (81 ^ 2 + (-108) ^ 2) * (z.re ^ 2 + z.im ^ 2), this will simplify to goal, as z.re^2 + z.im^2 = 16
    have h_ineq := hcs 81 (-108) (z.re) (z.im)
    rw [this] at h_ineq
    have h_ineq : (81 * z.re + -108 * z.im) ^ 2 ≤ 540^2 := by
      norm_num; norm_num at h_ineq; assumption
    convert_to 81 * z.re + - 108 * z.im ≤ 540
    . ring
    . refine le_of_sq_le_sq h_ineq ?_
      norm_num