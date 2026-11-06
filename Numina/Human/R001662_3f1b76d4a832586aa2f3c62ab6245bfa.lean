import Mathlib
open MvPolynomial Polynomial

/- Prove that if f is homogeneous, then f (zx, zy) = z^n f(x, y) -/
lemma eval_mul_eq_mul_eval_of_isHomogeneous {n : ℕ} (f : MvPolynomial (Fin 2) ℝ)
    (hf : f.IsHomogeneous n) {x y z : ℝ} : f.eval ![z * x, z * y] = z ^ n * f.eval ![x, y] := by
  -- Prove by induction on f
  induction f using MvPolynomial.induction_on'' generalizing n
  · -- If f = a for some a ∈ ℝ, then f is homogeneous of degree 0
    rename_i a
    by_cases ha : a ≠ 0
    · have : (MvPolynomial.C (σ := Fin 2) a).IsHomogeneous 0 := by exact isHomogeneous_C (Fin 2) a
      apply IsHomogeneous.inj_right hf at this
      simp [ha] at this
      simp [this]
    · simp at ha
      simp [ha]
  · -- If f = (MvPolynomial.monomial a) b + f', then f is homogeneous of degree n if and only if
    -- (MvPolynomial.monomial a) b and f' are homogeneous of degree n
    -- We can apply the induction hypothesis to f' and (MvPolynomial.monomial a) b and obtain the result
    rename_i a b f ha hb ih₁ ih₂
    have h₀ : ((MvPolynomial.monomial a) b).IsHomogeneous n := by
      intro c hc
      have hc' : (((MvPolynomial.monomial a) b) + ↑f).coeff c ≠ 0 := by
        simp only [MvPolynomial.coeff_add]
        have : MvPolynomial.coeff c f = 0 := by
          simp at hc
          simp [hc.1] at ha
          exact ha
        simp only [this, add_zero]
        exact hc
      exact hf hc'
    have h₁ : IsHomogeneous f n := by
      intro c hc
      have hc' : (MvPolynomial.monomial a b + ↑f).coeff c ≠ 0 := by
        simp only [MvPolynomial.coeff_add]
        have : MvPolynomial.coeff c ((MvPolynomial.monomial a) b) = 0 := by
          simp [hb]
          simp at ha
          by_contra h
          simp [h] at ha
          exact hc.elim ha
        simp [this, hc]
      exact hf hc'
    apply ih₁ at h₁
    apply ih₂ at h₀
    simp [h₀, h₁]
    ring
  · -- If f = p * MvPolynomial.X k, then f is homogeneous of degree n if and only if
    -- p is homogeneous of degree n - 1
    -- We can apply the induction hypothesis to p and obtain the result.
    rename_i p k ih
    have h₀ : (MvPolynomial.X (R := ℝ) k).IsHomogeneous 1 := by exact isHomogeneous_X ℝ k
    have h₁ : p.IsHomogeneous (n - 1) := by
      intro c hc
      let c' := c + fun₀ | k => 1
      have hc' : (p * MvPolynomial.X k).coeff c' ≠ 0 := by
        simp [c', MvPolynomial.coeff_mul_X]
        exact hc
      obtain hf := hf hc'
      simp [c'] at hf
      have : (Finsupp.weight 1) (fun₀ | k => 1) = 1 := by
        simp [Finsupp.weight]
      simp [this] at hf
      exact Nat.eq_sub_of_add_eq hf
    by_cases hn : n = 0
    · simp [hn] at h₁
      have : (p * MvPolynomial.X k).IsHomogeneous 1 := by
        rw [show 1 = 0 + 1 by rfl]
        exact IsHomogeneous.mul h₁ h₀
      apply IsHomogeneous.inj_right hf at this
      simp [hn] at this
      simp [this]
    · apply ih at h₁
      simp [h₁]
      nth_rw 2 [show n = (n - 1) + 1 by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]]
      rw [pow_add]
      fin_cases k
      all_goals simp; ring

/- We prove that if f is homogeneous and f's degree is one, then f = aX + bY for some a b. -/
lemma eq_add_mul_of_isHomogeneous_one (f : MvPolynomial (Fin 2) ℝ) (hf : f.IsHomogeneous 1) :
    ∃ a b : ℝ, ∀ x, f.eval x = a * x 0 + b * x 1 := by
  -- Prove by induction on f
  induction f using MvPolynomial.induction_on''
  · -- If f = a for some a ∈ ℝ, then f is homogeneous of degree 0, contradiction.
    rename_i a
    by_cases ha : a ≠ 0
    · have : (MvPolynomial.C (σ := Fin 2) a).IsHomogeneous 0 := by exact isHomogeneous_C (Fin 2) a
      apply IsHomogeneous.inj_right hf at this
      simp [ha] at this
    · simp at ha
      use 0, 0
      simp [ha]
  · -- If f = (MvPolynomial.monomial a) b + f', then f is homogeneous of degree 1 if and only if
    -- (MvPolynomial.monomial a) b and f' are homogeneous of degree 1
    -- We can apply the induction hypothesis to f' and (MvPolynomial.monomial a) b and obtain the result
    rename_i a b f ha hb ih₁ ih₂
    have h₀ : ((MvPolynomial.monomial a) b).IsHomogeneous 1 := by
      intro c hc
      have hc' : (((MvPolynomial.monomial a) b) + ↑f).coeff c ≠ 0 := by
        simp only [MvPolynomial.coeff_add]
        have : MvPolynomial.coeff c f = 0 := by
          simp at hc
          simp [hc.1] at ha
          exact ha
        simp only [this, add_zero]
        exact hc
      exact hf hc'
    have h₁ : IsHomogeneous f 1 := by
      intro c hc
      have hc' : (MvPolynomial.monomial a b + ↑f).coeff c ≠ 0 := by
        simp only [MvPolynomial.coeff_add]
        have : MvPolynomial.coeff c ((MvPolynomial.monomial a) b) = 0 := by
          simp [hb]
          simp at ha
          by_contra h
          simp [h] at ha
          exact hc.elim ha
        simp [this, hc]
      exact hf hc'
    apply ih₁ at h₁
    apply ih₂ at h₀
    obtain ⟨a₁, b₁, h₁⟩ := h₁
    obtain ⟨a₂, b₂, h₂⟩ := h₀
    use a₁ + a₂, b₁ + b₂
    intro x
    simp [h₁, h₂]
    ring
  · -- If f = p * MvPolynomial.X k, then f is homogeneous of degree 1 if and only if
    -- p is homogeneous of degree 0
    -- Then p = a for some a ∈ ℝ, and the result follows.
    rename_i p k ih
    have h₀ : (MvPolynomial.X (R := ℝ) k).IsHomogeneous 1 := by exact isHomogeneous_X ℝ k
    have h₁ : p.IsHomogeneous 0 := by
      intro c hc
      let c' := c + fun₀ | k => 1
      have hc' : (p * MvPolynomial.X k).coeff c' ≠ 0 := by
        simp [c', MvPolynomial.coeff_mul_X]
        exact hc
      obtain hf := hf hc'
      simp [c'] at hf
      have : (Finsupp.weight 1) (fun₀ | k => 1) = 1 := by
        simp [Finsupp.weight]
      simp [this] at hf
      exact hf
    apply totalDegree_zero_iff_isHomogeneous _ |>.mpr at h₁
    apply totalDegree_eq_zero_iff_eq_C.mp at h₁
    rw [h₁]
    fin_cases k
    · use p.coeff 0, 0
      simp
    · use 0, p.coeff 0
      simp

/- We show that there exists a polynomial P such that P(x) = f(x, 1 - x). -/
lemma exists_poly_for_mvpolynomial (f : MvPolynomial (Fin 2) ℝ) : ∃ P : ℝ[X], ∀ x, P.eval x = f.eval ![x, 1 - x] := by
  -- Prove by induction on f
  induction f using MvPolynomial.induction_on
  · -- If f = a for some a ∈ ℝ, then P = a
    rename_i a
    simp
    use Polynomial.C a
    simp
  · -- If f = p + q, then we can apply the induction hypothesis to p and q and obtain the result
    rename_i p q ih₁ ih₂
    obtain ⟨P₁, h₁⟩ := ih₁
    obtain ⟨P₂, h₂⟩ := ih₂
    use P₁ + P₂
    intro x
    simp [h₁, h₂]
  · -- If f = p * MvPolynomial.X k, then we can apply the induction hypothesis to p and obtain P.
    -- Then P * [X, 1 - X] k is the desired polynomial.
    rename_i a b ih
    obtain ⟨P, h⟩ := ih
    simp
    use P * ![Polynomial.X, 1 - Polynomial.X] b
    intro x
    simp [h]
    left
    fin_cases b
    all_goals simp

/- We show that if x + y = 1, then f(x,y) = x - 2y  -/
lemma eq_X_sub_two_Y (f : MvPolynomial (Fin 2) ℝ)
    (h1 : f.eval ![1, 0] = 1)
    (h2 : ∀ a b c : ℝ, f.eval ![a + b, c] + f.eval ![b + c, a] + f.eval ![c + a, b] = 0)
    {x y : ℝ} (hxy : x + y = 1) :
    f.eval ![x, y] = x - 2 * y := by

  -- obtain a polynomial P such that P(x) = f(x, 1 - x)
  obtain ⟨P, hP⟩ := exists_poly_for_mvpolynomial f
  -- let F(x) = P(x) - (3x - 2)
  let F : ℝ[X] := P - (3 * Polynomial.X - 2)
  have hFeval {x : ℝ} : F.eval x = f.eval ![x, 1 - x] - (3 * x - 2) := by
    simp [F, hP]

  -- By the condition, we have F(x) + 2F(1 - x / 2) = 0
  have hF {x : ℝ} : F.eval x + 2 * F.eval (1 - x / 2) = 0 := by
    obtain h2 := h2 (x / 2) (x / 2) (1 - x)
    ring_nf at h2
    rw [hFeval, hFeval, ←h2]
    ring_nf

  -- Through a simple induction, we can show that F((2 + (-2)^k) / 3) = 0 for all k ∈ ℕ
  have hF {k : ℕ} : F.eval ((2 + (-2) ^ k) / 3) = 0 := by
    induction k with
    | zero =>
      simp [hFeval]
      ring_nf
      rw [h1]
      simp
    | succ k ih =>
      trans -2 * F.eval (1 - (2 + (-2) ^ (k + 1)) / 3 / 2)
      · apply sub_eq_zero.mp
        simp [hF]
      trans -2 * F.eval ((2 + (-2) ^ k) / 3)
      · congr
        ring
      · rw [ih]
        simp
  -- Since F has infinitely many roots, F = 0
  have hF : F = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hsub : {x | F.IsRoot x} ⊇ (Set.univ : Set ℕ).image (fun k => (2 + (-2) ^ k) / 3) := by
      intro x hx
      simp at hx
      obtain ⟨k, hk⟩ := hx
      simp [←hk]
      exact hF
    apply Set.Infinite.mono hsub
    refine Set.Infinite.image ?_ ?_
    · intro k₁ hk₁ k₂ hk₂ h
      field_simp at h
      apply congrArg abs at h
      simp at h
      exact h
    · exact Set.infinite_univ

  -- Therefore, f(x, 1 - x) = 3x -2 = x - 2y
  simp [hF] at hFeval
  have hy : y = 1 - x := by linarith only [hxy]
  rw [hy]
  obtain h := hFeval (x := x)
  rw [eq_comm] at h
  apply sub_eq_zero.mp at h
  rw [h]
  ring


/- 10. (GBR) ${ }^{\mathrm{IMO} 6}$ The function $f(x, y)$ is a homogeneous polynomial of the $n$th degree in $x$ and $y$. If $f(1,0)=1$ and for all $a, b, c$,  $$ f(a+b, c)+f(b+c, a)+f(c+a, b)=0 $$  prove that $f(x, y)=(x-2 y)(x+y)^{n-1}$. -/
theorem algebra_25041 {n : ℕ} (hn : n > 0) (f : MvPolynomial (Fin 2) ℝ) (hf : f.IsHomogeneous n)
    (h1 : f.eval ![1, 0] = 1)
    (h2 : ∀ a b c : ℝ, f.eval ![a + b, c] + f.eval ![b + c, a] + f.eval ![c + a, b] = 0) :
    f = (X 0 - 2 * X 1) * (X 0 + X 1) ^ (n - 1) := by

  apply MvPolynomial.funext
  intro x
  simp
  have hn : n ≥ 1 := hn
  rcases gt_or_eq_of_le hn with hn | hn
  · -- If n > 1, we divide into two cases: x 0 + x 1 = 0 and x 0 + x 1 ≠ 0
    by_cases hx : x 0 + x 1 = 0
    · -- If x 0 + x 1 = 0, then x 1 = -x 0, we nneed to show that f(x 0, x 1) = 0.
      -- By the condition, we have f(x 0, x 1) + 2f(x 0 / 2, x 1 / 2) = 0
      simp [hx]
      obtain h2 := h2 (x 0 / 2) (x 0 / 2) (- x 0)
      simp [hx] at h2
      ring_nf at h2
      -- Since f is homogeneous, we have f(x 0 / 2, x 1 / 2) = (1 / 2)^n * f(x 0, x 1)
      have hx' : x 1 = - x 0 := by
        apply sub_eq_zero.mp
        simp [←hx]
        ring
      have : f.eval ![x 0, -x 0] = f.eval ![x 0, x 1] := by
        rw [hx']
      rw [this] at h2
      have : f.eval ![x 0 * (-1 / 2), x 0 * (1 / 2)] = f.eval ![(-1 / 2) * x 0, (-1 / 2) * x 1] := by
        rw [hx']
        congr
        ext i
        fin_cases i
        all_goals simp; ring
      -- Therefore, we have (1 + (-1 / 2)^n * 2) * f(x 0, x 1) = 0
      rw [this, eval_mul_eq_mul_eval_of_isHomogeneous f hf] at h2
      have : (1 + (-1 / 2) ^ n * 2) * (f.eval x) = 0 := by
        have : x = ![x 0, x 1] := by
          ext i
          fin_cases i
          all_goals simp
        rw [this, ←h2]
        ring
      simp at this
      rcases this with h | h
      · -- Note that 1 + (-1 / 2)^n * 2 ≠ 0.
        have : (-1 / 2 : ℝ) ^ n = (-1 / 2) ^ 1 := by linarith only [h]
        apply congrArg abs at this
        rw [abs_pow, abs_pow] at this
        apply pow_right_injective₀ (by positivity) (by simp [abs_div]) at this
        simp [this] at hn
      · -- So f(x 0, x 1) = 0.
        simp [h]
        right
        apply ne_of_gt
        simp
        exact hn
    · -- If x 0 + x 1 ≠ 0, then we can divide by x 0 + x 1,
      -- Then f (x 0, x 1) = (x 0 + x 1)^n * f (x 0 / (x 0 + x 1), x 1 / (x 0 + x 1))
      simp at hx
      have hx : x = ![(x 0 + x 1) * (x 0 / (x 0 + x 1)), (x 0 + x 1) * (x 1 / (x 0 + x 1))] := by
        ext i
        fin_cases i
        all_goals field_simp [hx]
      nth_rw 1 [hx]
      -- Since x 0 / (x 0 + x 1) + x 1 / (x 0 + x 1) = 1, we can apply the previous lemma.
      -- Therefore, f(x 0, x 1) = (x 0 + x 1)^n * (x 0 / (x 0 + x 1) - 2 * x 1 / (x 0 + x 1)) = (x 0 - 2 * x 1) * (x 0 + x 1)^(n - 1)
      rw [eval_mul_eq_mul_eval_of_isHomogeneous f hf]
      rw [eq_X_sub_two_Y f h1 h2]
      · field_simp
        have hn : n = n - 1 + 1 := by
          rw [Nat.sub_add_cancel (by assumption)]
        nth_rw 1 [hn]
        ring
      · field_simp
  · -- If n = 1, then f = aX + bY for some a b.
    -- By the first condition, we have a = 1.
    -- By the second condition, we have b = -2.
    simp [hn] at hf
    apply eq_add_mul_of_isHomogeneous_one f at hf
    obtain ⟨a, b, h⟩ := hf
    simp [h, hn]
    obtain h2 := h2 1 1 1
    simp [h] at h2 h1
    simp [h1] at h2
    have hb : b = - 2 := by linarith only [h2]
    rw [h1, hb]
    -- Therefore, f = X - 2Y.
    ring
