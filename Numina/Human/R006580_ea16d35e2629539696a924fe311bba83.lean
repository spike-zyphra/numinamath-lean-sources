import Mathlib

noncomputable def α (n : ℕ) := 2 * Real.arctan ↑n

lemma lemma_range_α : 0 ≤ α n ∧ α n < Real.pi := by
  simp [α]
  constructor
  . rw [←Real.arctan_zero]
    apply Real.arctan_le_arctan
    simp
  . have := Real.arctan_mem_Ioo n
    simp at this
    linarith

lemma lemma_α_def_inv : (α n / 2).tan = n := by simp [α]

lemma lemma_cos_nonneg : (α n / 2).cos ≠ 0 := by
  simp [α, Real.cos_arctan]
  by_contra! h
  have h1 : (0 : ℝ) < 1 + ↑n ^ 2 := by
    apply add_pos_of_pos_of_nonneg
    . simp
    . apply pow_two_nonneg
  rw [Real.sqrt_eq_iff_mul_self_eq (le_of_lt h1) (by simp)] at h
  linarith

lemma lemma_sin_rational : ∃ d : ℚ, (α n).sin = d := by
  use 2 * n / (1 + n ^ 2)
  push_cast
  rw [←lemma_α_def_inv]
  rw [show α n = 2 * (α n / 2) by ring, Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  field_simp [lemma_cos_nonneg]
  ring

lemma lemma_cos_rational : ∃ d : ℚ, (α n).cos = d := by
  use (1 - n ^ 2) / (1 + n ^ 2)
  push_cast
  rw [←lemma_α_def_inv]
  rw [show α n = 2 * (α n / 2) by ring, Real.cos_two_mul', Real.tan_eq_sin_div_cos]
  field_simp [lemma_cos_nonneg]

-- We construct a sequence of points P_i on the unit circle
noncomputable def P (n : ℕ) : ℂ := {
  re := (2 * α n).cos,
  im := (2 * α n).sin,
}

lemma lemma_P_inj : Function.Injective P := by
  simp [Function.Injective]
  -- Specifically, if $P_m=P_n$
  intros m n h
  simp [P] at h
  rcases h with ⟨h1, h2⟩
  have := Real.Angle.cos_sin_inj h1 h2
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at this
  -- then $2\alpha_m \equiv 2\alpha_n \pmod{2\pi}$
  obtain ⟨k, hk⟩ := this
  have : k = 0 := by
    suffices (-1 : ℝ) < ↑k ∧ ↑k < (1 : ℝ) by
      norm_cast at this
      simp at this
      omega
    constructor
    all_goals
    refine lt_of_mul_lt_mul_left (a := 2 * Real.pi) ?_ (by simp [Real.pi_nonneg])
    rw [←hk]
    -- Since $2\alpha_m, 2\alpha_n \in [0,2\pi)$
    have := lemma_range_α (n := n)
    have := lemma_range_α (n := m)
    linarith
  -- this means $\alpha_j=\alpha_k$
  simp [α, this] at hk
  ring_nf at hk
  have : Real.arctan ↑m = Real.arctan ↑n := by linarith
  have := Real.arctan_injective this
  norm_cast at this

-- The distance of two points on the unit circle can be expressed in a convenient way
lemma lemma_dist : dist (P m) (P n) = |2 * (α m - α n).sin| := by
  simp [P]
  rw [Real.sqrt_eq_iff_mul_self_eq ?hx (by simp), abs_mul_abs_self]
  case hx => apply add_nonneg <;> apply pow_two_nonneg
  conv =>
    lhs
    ring_nf
    repeat rw [Real.sin_sq]
    ring_nf
    rhs
    rw [←neg_add', ←add_mul, ←Real.cos_sub, ←sub_mul]
  ring_nf
  rw [Real.sin_sq_eq_half_sub]
  ring_nf

/- Let $N$ be a positive integer. Prove that there exists a set $s$ containing $N$ distinct points on the unit circle in the Euclidean plane such that for any two distinct points $P_1, P_2 \in s$, the distance between $P_1$ and $P_2$ is a rational number.
-/
theorem number_theory_638697 (N : ℕ) (_hN : N > 0) :
  ∃ (s : Finset ℂ), s.card = N ∧ (∀ P ∈ s, ‖P‖ = 1) ∧
  (∀ P ∈ s, ∀ Q ∈ s, P ≠ Q → ∃ (d : ℚ), dist P Q = d) := by
  use (Finset.range N).map ⟨P, lemma_P_inj⟩
  constructor
  . simp
  constructor
  . simp
    intro n h
    simp [P, Complex.abs_eq_sqrt_sq_add_sq]
  . simp
    intro m _ n _ _
    -- For the distance, we require $\sin(\alpha_m - \alpha_n)$ to be rational
    rw [lemma_dist]
    -- and $\sin(\alpha_m - \alpha_n) = \sin\alpha_m\cos\alpha_n - \cos\alpha_m\sin\alpha_n$ is rational
    rw [Real.sin_sub]
    -- since $\sin\alpha_m, \cos\alpha_m, \sin\alpha_n, \cos\alpha_n$ are all rational
    let ⟨d1, h1⟩ := lemma_sin_rational (n := m)
    let ⟨d2, h2⟩ := lemma_sin_rational (n := n)
    let ⟨d3, h3⟩ := lemma_cos_rational (n := m)
    let ⟨d4, h4⟩ := lemma_cos_rational (n := n)
    rw [h1, h2, h3, h4]
    norm_cast
    simp
