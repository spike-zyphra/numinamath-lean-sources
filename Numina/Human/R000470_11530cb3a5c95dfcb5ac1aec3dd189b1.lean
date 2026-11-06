import Mathlib

/-The polynomial $x^{101} + Ax + B$ is divisible by $x^2 + x + 1$ for some real numbers $A$ and $B.$  Find $A + B.$-/
theorem algebra_11003 {A B : ℝ} (h : ∀ x : ℂ, (x^2 + x + 1) ∣ x^101 + A * x + B) : A + B = 2 := by
  --If $x^{101} + Ax + B$ is divisible by $x^2 + x + 1,$ then $x^{101} + Ax + B$ must be equal to 0 any time $x$ is a root of $x^2 + x + 1 = 0.$
  have eq : ∀x : ℂ, (x^2 + x + 1) = 0 → (x^101 + A * x + B) = 0 := by
    intro x hx
    have := h x
    rcases this with ⟨y, hy⟩
    rw [hx] at hy
    simp at hy
    exact hy
  --Let $ω$ be a root of $x^2 + x + 1 = 0,$ so $ω^2 + ω + 1 = 0.$  Then
  have : ∃(ω : ℂ), ω^2 + ω + 1 = 0 ∧ ω.im ≠ 0 := by
    use (-1/2 : ℂ) + √3 * Complex.I / 2
    field_simp
    rw [add_pow_two, mul_pow, Complex.I_sq]
    norm_cast
    rw [Real.sq_sqrt]
    field_simp
    ring_nf
    linarith
  rcases this with ⟨ω, ⟨hω, not_real_ω⟩⟩

  -- Let $ω$ be a root of $x^2 + x + 1 = 0,$ so $ω^2 + ω + 1 = 0.$  Then \[(ω - 1)(ω^2 + ω + 1) = 0,\]or $ω^3 - 1 = 0,$ which means $ω^3 = 1.
  have ω_pow_3 : (ω - 1) * (ω^2 + ω + 1) = 0 := by
    rw [hω]
    simp
  rw [sub_mul, mul_add, mul_add, one_mul, mul_one, ←sub_sub, ←sub_sub] at ω_pow_3
  rw [←pow_two, mul_comm, ←pow_succ, two_add_one_eq_three] at ω_pow_3
  rw [add_comm, ←add_assoc, ←add_sub, sub_self, add_zero, add_comm, ←add_sub, sub_self, add_zero] at ω_pow_3
  rw [sub_eq_zero] at ω_pow_3

  -- By the Factor Theorem, ω^{101} + A ω + B = 0.
  have eq := eq ω hω
  -- We have that  ω^101 = ω^{3 * 33 + 2} = (ω^3)^{33} * ω^2 = ω^2
  have ω_pow_101 : ω^101 = ω^2 := by
    have : 101 = 3 * 33 + 2 := by linarith
    rw [this, pow_add, pow_mul, ω_pow_3]
    simp
  -- so, ω ^ 101 + ↑A * ω + ↑B = ω^2 + ↑A * ω + ↑B = 0
  rw [ω_pow_101] at eq
  -- = (-ω - 1) + A ω + B
  have : ω ^ 2 + ↑A * ω + ↑B = (- ω - 1) + A * ω + B := by
    field_simp
    rw [←sub_eq_zero, ←sub_add, sub_neg_eq_add]
    exact hω
  rw [this] at eq
  -- (A - 1) ω + (B - 1) = 0
  have : (- ω - 1) + A * ω + B = (A - 1) * ω + (B - 1) := by ring_nf
  rw [this] at eq

  -- Since $ω$ is a nonreal complex number, we must have $A = 1$
  have eq2 : ((↑A - 1) * ω + (↑B - 1)).im = 0 := by
    rw [eq]
    simp
  rw [Complex.add_im] at eq2
  simp [not_real_ω, sub_eq_zero] at eq2

  -- and $B = 1,$ so $A + B = \boxed{2}.
  rw [eq2] at eq
  simp [sub_eq_zero] at eq
  rw [eq, eq2, one_add_one_eq_two]
