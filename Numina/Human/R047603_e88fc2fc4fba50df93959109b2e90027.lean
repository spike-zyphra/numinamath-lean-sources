import Mathlib

open Real

namespace algebra_24619

abbrev ℚ_of_ℝ := Set.range (↑· : ℚ → ℝ)

abbrev tan_defined_at x := ∀ k : ℤ, x ≠ (2 * k + 1) * π / 2

theorem tan_sub' {x y : ℝ}
    (h : tan_defined_at x ∧ tan_defined_at y) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
  rcases h with ⟨tan_defined_at_x, tan_defined_at_y⟩
  have := tan_add' (x := x) (y := -y) ⟨
    tan_defined_at_x,
    by
      intro k
      have := tan_defined_at_y (- k - 1)
      --norm_num at *
      norm_num at this
      --linarith
      intro h
      --linarith
      have : y = (2 * (-↑k - 1) + 1) * π / 2 := by linarith
      contradiction
    ⟩
  simp at this
  exact this

/- 15. (GDR 3) Suppose $\tan \alpha=p / q$, where $p$ and $q$ are integers and $q \neq 0$. Prove that the number $\tan \beta$ for which $\tan 2 \beta=\tan 3 \alpha$ is rational only when $p^{2}+q^{2}$ is the square of an integer. -/
theorem algebra_24619 {α β : ℝ} {p q : ℤ}
    (tan_defined_at_α : tan_defined_at α) (tan_defined_at_3α : tan_defined_at (3 * α))
    (tan_defined_at_β : tan_defined_at β) (tan_defined_at_2β : tan_defined_at (2 * β))
    (q_ne_0 : q ≠ 0)
    (tan_α_eq : tan α = p / q)
    (tan_2β_eq_tan_3α : tan (2 * β) = tan (3 * α)) :
    tan β ∈ ℚ_of_ℝ ↔ IsSquare (p ^ 2 + q ^ 2) := by
  -- 15. Given that $\tan \alpha \in \mathbb{Q}$, we have that $\tan \beta$ is rational if and only if $\tan \gamma$ is rational, where $\gamma=\beta-\alpha$ and $2 \gamma=\alpha$ (this is incorrect from the reference solution).
  let γ := β - α
  have iff₁ : tan β ∈ ℚ_of_ℝ ↔ tan γ ∈ ℚ_of_ℝ := by
    have tan_γ_eq : tan γ = (tan β - tan α) / (1 + tan β * tan α) :=
      tan_sub' ⟨tan_defined_at_β, tan_defined_at_α⟩
    constructor
    . intro tan_β_in_ℚ_of_ℝ
      rcases tan_β_in_ℚ_of_ℝ with ⟨tan_β_ℚ, tan_β_cast_eq⟩
      dsimp at tan_β_cast_eq
      rw [←tan_β_cast_eq, tan_α_eq] at tan_γ_eq
      --norm_cast at tan_γ_eq -- not needed
      --qify at tan_γ_eq -- doesn't work
      --conv_rhs at tan_γ_eq => qify -- doesn't work
      --simp -- not needed
      exact ⟨
        _ /- (tan_β_ℚ - p / q) / (1 + tan_β_ℚ * (p / q)) -/,
        by
          convert tan_γ_eq.symm using 1
          norm_cast
      ⟩
    . by_cases h : 1 + tan β * tan α = 0
      . rw [h] at tan_γ_eq
        norm_num at tan_γ_eq
        have : tan β * tan α = - 1 := by linarith
        have : tan β = - 1 / tan α := by calc
          tan β = tan β * tan α / tan α := by
            have : tan α ≠ 0 := by
              intro eq_0
              simp [eq_0] at this
            field_simp
          _ = - 1 / tan α := by rw [this]
        intro
        rw [tan_α_eq] at this
        exact ⟨_, by
          convert this.symm using 1
          norm_cast
        ⟩
      . by_cases 1 - tan α * tan γ = 0
        . -- `tan β` is actually undefined here.
          have := cos_add α γ
          have mul_eq_1 : tan α * tan γ = 1 := by linarith
          rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos] at mul_eq_1
          field_simp at mul_eq_1
          have : cos α * cos γ ≠ 0 := by
            intro eq_0
            -- `simpa [eq_0]` worked when `mul_eq_1` was not named.
            simp [eq_0] at mul_eq_1
          have : sin α * sin γ = cos α * cos γ := by calc
            sin α * sin γ = sin α * sin γ / (cos α * cos γ) * (cos α * cos γ) := by field_simp
            _ = cos α * cos γ := by rw [mul_eq_1]; simp
          have : cos β = 0 := by
            rw [show β = α + γ by ring]
            rw [cos_add]
            linarith
          exfalso
          rcases cos_eq_zero_iff.mp this with ⟨k, _⟩
          have := tan_defined_at_β k
          contradiction
        . have tan_β_eq : tan β = (tan α + tan γ) / (1 - tan α * tan γ) := by
            --field_simp [tan_γ_eq, h]
            have : tan γ * (1 + tan β * tan α) = tan β - tan α := by
              field_simp [tan_γ_eq, h]
            have : tan β * (1 - tan α * tan γ) = tan α + tan γ := by
              linarith
            field_simp [this]
          rintro ⟨tan_γ_ℚ, tan_γ_cast_eq⟩
          dsimp at tan_γ_cast_eq
          rw [←tan_γ_cast_eq, tan_α_eq] at tan_β_eq
          exact ⟨_, by
            convert tan_β_eq.symm using 1
            norm_cast
          ⟩
  -- Putting $t=\tan \gamma$ we obtain $\frac{p}{q}=\tan 2 \gamma=\frac{2 t}{1-t^{2}}$, which leads to the quadratic equation $p t^{2}+2 q t-p=0$. This equation has rational solutions if and only if its discriminant $4\left(p^{2}+q^{2}\right)$ is a perfect square, and the result follows.
  have iff₂ : tan γ ∈ ℚ_of_ℝ ↔ IsSquare (p ^ 2 + q ^ 2) := by
    have _2γ_equiv_α : sin (2 * γ) * cos α = sin α * cos (2 * γ) := by
      let left := 2 * β - 2 * α
      let right := 3 * α - 2 * α
      rw [show α = 3 * α - 2 * α by ring] -- must be before the next one
      rw [show 2 * γ = 2 * β - 2 * α by ring]
      rw [sin_sub, cos_sub, sin_sub, cos_sub]
      have : ∃ a ≠ 0, sin (2 * β) = a * sin (3 * α) ∧ cos (2 * β) = a * cos (3 * α) := by
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos] at tan_2β_eq_tan_3α
        have cos_2β_ne_0 : cos (2 * β) ≠ 0 := cos_ne_zero_iff.mpr tan_defined_at_2β
        have cos_3α_ne_0 : cos (3 * α) ≠ 0 := cos_ne_zero_iff.mpr tan_defined_at_3α
        let a := cos (2 * β) / cos (3 * α)
        have a_ne_0 : a ≠ 0 := by unfold a; exact div_ne_zero cos_2β_ne_0 cos_3α_ne_0
        have cos_eq : cos (2 * β) = a * cos (3 * α) := by unfold a; field_simp
        have sin_eq : sin (2 * β) = a * sin (3 * α) := by
          --field_simp [tan_2β_eq_tan_3α, cos_2β_ne_0, cos_3α_ne_0]
          --nlinarith
          calc
            sin (2 * β) = (sin (2 * β) / cos (2 * β)) * cos (2 * β) := by field_simp
            _ = (sin (3 * α) / cos (3 * α)) * cos (2 * β) := by congr
            _ = a * sin (3 * α) := by unfold a; field_simp; ring
        use a, a_ne_0
      rcases this with ⟨a, a_ne_0, sin_eq_a_mul, cos_eq_a_mul⟩
      rw [sin_eq_a_mul, cos_eq_a_mul]
      ring
    let t := tan γ
    have /- quadratic_equation_t -/ : p * t ^ 2 + 2 * q * t - p = 0 := by
      by_cases t_sq_eq : t ^ 2 = 1
      . suffices ¬ tan_defined_at α by contradiction
        unfold t at t_sq_eq
        rw [tan_eq_sin_div_cos] at t_sq_eq
        field_simp at t_sq_eq
        have : cos γ ^ 2 ≠ 0 := by
          intro eq_0
          rw [eq_0] at t_sq_eq
          simp at t_sq_eq
        -- `nlinarith` or `field_simp` don't work directly here.
        have : sin γ ^ 2 = cos γ ^ 2 := by calc
          sin γ ^ 2 = sin γ ^ 2 / cos γ ^ 2 * cos γ ^ 2 := by field_simp
          _ = cos γ ^ 2 := by rw [t_sq_eq]; simp
        have : sin γ ^ 2 + cos γ ^ 2 = 1 := sin_sq_add_cos_sq γ --simp
        have cos_2γ_eq_0 : cos (2 * γ) = 0 := by
          rw [cos_two_mul]
          linarith
        have : sin (2 * γ) = 1 ∨ sin (2 * γ) = -1 := by
          have := sin_sq_add_cos_sq (2 * γ)
          have : sin (2 * γ) ^ 2 = 1 := by nlinarith
          simpa
        have : cos α = 0 := by
          rw [cos_2γ_eq_0] at _2γ_equiv_α
          rcases this <;>
          . nlinarith
        have := cos_eq_zero_iff.mp this
        unfold tan_defined_at
        push_neg
        exact this
      . rw [sin_two_mul] at _2γ_equiv_α
        by_cases whether_cos_γ_eq_0 : cos γ = 0
        . have sin_α_eq_0 : sin α = 0 := by
            simp [cos_two_mul, whether_cos_γ_eq_0] at _2γ_equiv_α
            exact _2γ_equiv_α
          have : tan α = 0 := by
            have := tan_eq_sin_div_cos α
            simp [sin_α_eq_0] at this
            exact this
          have p_eq_0 : p = 0 := by
            simp [tan_α_eq, q_ne_0] at this
            exact this
          -- `tan γ` is actually not defined here.
          have t_eq_0 : t = 0 := by
            /-
            have : sin γ ≠ 0 := by
              simp [whether_cos_γ_eq_0] at sin_γ_sq_add_cos_γ_sq
              cases sin_γ_sq_add_cos_γ_sq <;> linarith
             -/
            have := tan_eq_sin_div_cos γ
            simp [whether_cos_γ_eq_0] at this
            exact this
          simp [p_eq_0, t_eq_0]
        . simp [cos_two_mul'] at _2γ_equiv_α
          have := tan_mul_cos whether_cos_γ_eq_0
          rw [←this] at _2γ_equiv_α
          have cos_α_ne_0 := cos_ne_zero_iff.mpr tan_defined_at_α
          have := tan_mul_cos cos_α_ne_0
          rw [←this] at _2γ_equiv_α
          simp [tan_α_eq] at _2γ_equiv_α
          have cos_pows_mul_p_div_q_t_poly_eq_0 : (cos γ ^ 2 * cos α) * ((p / q) * t ^ 2 + 2 * t - (p / q)) = 0 := by linarith
          have p_div_q_t_poly_eq_0 : (p / q) * t ^ 2 + 2 * t - (p / q) = 0 := by
            simp at cos_pows_mul_p_div_q_t_poly_eq_0
            rcases cos_pows_mul_p_div_q_t_poly_eq_0 with (_ | _) | _
            . contradiction
            . contradiction
            . assumption
          have : p * t ^ 2 + 2 * q * t - p = q * ((p / q) * t ^ 2 + 2 * t - (p / q)) := by
            field_simp
            ring
          rw [this, p_div_q_t_poly_eq_0]
          simp
    have quadratic_equation_t : p * (t * t) + 2 * q * t  + (- p) = 0 := by
      linarith
    --conv_lhs => rw [show tan γ = t from rfl]
    constructor
    . rintro ⟨t_ℚ, t_cast_eq⟩
      conv at quadratic_equation_t =>
        unfold t
        rw [←t_cast_eq]
        dsimp
        norm_cast
        --qify
        --push_cast
      push_cast at quadratic_equation_t -- `qify` works too.
      have := discrim_eq_sq_of_quadratic_eq_zero quadratic_equation_t
      unfold discrim at this
      conv_lhs at this => ring_nf
      have : p ^ 2 + q ^ 2 = (p * t_ℚ + q) * (p * t_ℚ + q) := by
        linarith
      have : IsSquare (p ^ 2 + q ^ 2 : ℚ) :=
        ⟨_, this⟩
      norm_cast at this
    . rintro ⟨r, p_sq_add_q_sq_eq⟩
      by_cases whether_p_eq_0 : p = 0
      . simp [whether_p_eq_0, q_ne_0] at quadratic_equation_t
        have : (0 : ℚ) = t := by norm_cast; symm; assumption
        --rw [show tan γ = t from rfl]
        exact ⟨0, this⟩
      . have isSq_d : IsSquare (discrim p (2 * q) (-p)) := by
          norm_num [discrim]
          ring_nf
          use (2 * r)
          ring_nf
          rw [show r ^ 2 = r * r by ring]
          rw [←p_sq_add_q_sq_eq]
          ring
        rcases isSq_d with ⟨r, d_eq_r_sq⟩
        rify at whether_p_eq_0
        unfold discrim at d_eq_r_sq
        rify at d_eq_r_sq
        have := (quadratic_eq_zero_iff /- (K := ℝ) (a := p) (b := 2 * q) (c := -p) -/ whether_p_eq_0 d_eq_r_sq t).mp quadratic_equation_t
        --qify at this
        rcases this with t_eq | t_eq
        . simp
          --norm_cast at t_eq
          exact ⟨(-(2 * q) + r) / (2 * p), by rify; exact t_eq.symm /- `by simp [t, t_eq]` for v4.19.0-rc3 -/⟩
        . simp
          exact ⟨(-(2 * q) - r) / (2 * p), by rify; exact t_eq.symm /- `by simp [t, t_eq]` for v4.19.0-rc3 -/⟩
  exact iff₁.trans iff₂

end algebra_24619
open algebra_24619
