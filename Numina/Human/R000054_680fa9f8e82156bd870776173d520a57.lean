import Mathlib

open Real

/- define cubic root -/
noncomputable abbrev croot (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.rpow x (1 / 3) else -Real.rpow (-x) (1 / 3)

/- cube after cubic root equal self -/
lemma aux_4188 (x : ℝ) : (croot x) ^ 3 = x := by
  simp [croot]
  split
  . rw [← rpow_natCast, ← rpow_mul (by assumption)]; simp
  norm_cast
  rw [neg_eq_neg_one_mul, mul_pow, Odd.neg_one_pow (by decide)]
  rw [← rpow_natCast, ← rpow_mul (by linarith)]
  simp

/- cubic root of nonpos is nonpos -/
lemma aux_nonpos_of_nonpos {x : ℝ} (h : x ≤ 0) : croot x ≤ 0 := by
  simp [croot]
  split
  . rw [show x = 0 by linarith]
    simp [show x = 0 by linarith]
  rw [neg_nonpos]
  exact rpow_nonneg (by linarith) 3⁻¹

/- cubic root of pos is pos -/
lemma aux_pos_of_pos {x : ℝ} (h : 0 < x) : 0 < croot x := by
  simp [croot]
  split
  . exact rpow_pos_of_pos h 3⁻¹
  linarith

/- cubic root of nonneg is nonneg -/
lemma aux_nonneg_of_nonneg {x : ℝ} (h : 0 ≤ x) : 0 ≤ croot x := by
  simp [croot]
  split
  . exact rpow_nonneg h 3⁻¹
  linarith

/- cubic root of neg is neg -/
lemma aux_neg_of_neg {x : ℝ} (h : x < 0) : croot x < 0:= by
  simp [croot]
  split
  . linarith
  rw [neg_neg_iff_pos]
  exact rpow_pos_of_pos (by linarith) 3⁻¹

/- solve x^2=y^2 where x,y have same sign -/
lemma aux_sq_eq_sq {x y : ℝ} (h : x ^ 2 = y ^ 2) (hxy : 0 ≤ x * y) :
    x = y := by
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h
  rcases h with _ | h
  . assumption
  nlinarith

/- Let the function $f: \mathbf{R} \rightarrow \mathbf{R}$ satisfy the condition $f\left(x^{3}+y^{3}\right)=(x+y) \cdot\left[(f(x))^{2}-f(x) \cdot f(y)+ f(f(y))^{2}\right]$ for all $x, y \in \mathbf{R}$. Prove that for all $x \in \mathbf{R}$, $f(1996 x)=1996 f(x)$.-/
theorem functional_equations_4188 {f : ℝ → ℝ} (h : ∀ x y, f (x^3+y^3) = (x+y)*(f x ^ 2 - f x * f y + (f y)^2)) :
    ∀ x, f (1996 * x) = 1996 * f x := by
  -- Set \(x = 0\) and \(y = 0\) in the functional equation:
  --  \[
  --  f(0^3 + 0^3) = (0 + 0) \left[(f(0))^2 - f(0)f(0) + f(f(0))^2\right]
  --  \]
  have h00 := h 0 0
  --  Simplifying, we get:
  --  \[
  --  f(0) = 0
  --  \]
  simp at h00
  -- Now, set \(y = 0\) in the functional equation:
  --  \[
  --  f(x^3 + 0^3) = (x + 0) \left[(f(x))^2 - f(x)f(0) + f(f(0))^2\right]
  --  \]
  have hx0 x := h x 0
  -- Since \(f(0) = 0\), the equation simplifies to:
  --  \[
  --  f(x^3) = x \cdot (f(x))^2
  --  \]
  simp [h00] at hx0
  -- Note that from the above relation, when \(x \geq 0\), \(f(x) \geq 0\) and when \(x \leq 0\), \(f(x) \leq 0\).
  have nonneg_of_nonneg {x} (hx : 0 ≤ x) : 0 ≤ f x := by
    rw [← aux_4188 x, hx0]
    apply mul_nonneg <| aux_nonneg_of_nonneg hx
    exact sq_nonneg _
  have nonpos_of_nonpos {x} (hx : x ≤ 0) : f x ≤ 0 := by
    rw [← aux_4188 x, hx0]
    apply mul_nonpos_of_nonpos_of_nonneg
    . exact aux_nonpos_of_nonpos hx
    . exact sq_nonneg _
  -- Define the set \(S\) as:
  --  \[
  --  S = \{a \mid a>0 \text{ and } f(ax) = af(x), \, \forall x \in \mathbb{R}\}
  --  \]
  let S : Set ℝ := {a | 0 < a ∧ ∀ x, f (a*x) = a*f x}
  -- Clearly, \(1 \in S\).
  have one_mem_S : 1 ∈ S := by simp [S]
  -- If \(a \in S\), demonstrate that \(a^{1/3} \in S\)
  have croot_mem_S {a} (ha : a ∈ S) : croot a ∈ S := by
    simp [S]
    constructor; exact aux_pos_of_pos ha.1
    intro x
    split; swap; linarith [ha.1]
    have h1 := hx0 (croot a * x)
    rw [mul_pow, aux_4188 a, ha.2, hx0] at h1
    rcases lt_trichotomy x 0 with hx | rfl | hx
    swap; simp [h00]
  --   By canceling the common terms and since the signs are the same:
  --  \[
  --  [a^{1/3} f(x)]^2 = [f(a^{1/3} x)]^2
  --  \]
    have H1 : (croot a * f x)^2=(f (croot a * x))^2 := by
      nth_rw 1 [← aux_4188 a] at h1
      have : croot a ≠ 0 := ne_of_gt <| aux_pos_of_pos <| ha.1
      rw [← mul_right_inj' (show x ≠ 0 by linarith)]
      rw [← mul_right_inj' this]
      linear_combination h1
    have hcroot : 0 < croot a := aux_pos_of_pos ha.1
    have : 0 ≤ (croot a * f x) * (f (croot a * x)) := by
      rw [mul_assoc]
      apply mul_nonneg <| le_of_lt hcroot
      apply mul_nonneg_of_nonpos_of_nonpos
      exact nonpos_of_nonpos <| le_of_lt hx
      apply nonpos_of_nonpos
      apply mul_nonpos_of_nonneg_of_nonpos
      exact le_of_lt hcroot
      exact le_of_lt hx
    have H2 := aux_sq_eq_sq H1 this
    have : croot a = a ^ ((3 : ℝ)⁻¹) := by
      unfold croot
      split
      apply congrArg
      norm_num
      linarith
    rw [this] at H2
    linear_combination -H2
    have H1 : (croot a * f x)^2=(f (croot a * x))^2 := by
      nth_rw 1 [← aux_4188 a] at h1
      have : croot a ≠ 0 := ne_of_gt <| aux_pos_of_pos <| ha.1
      rw [← mul_right_inj' (show x ≠ 0 by linarith)]
      rw [← mul_right_inj' this]
      linear_combination h1
    have hcroot : 0 < croot a := aux_pos_of_pos ha.1
    have : 0 ≤ (croot a * f x) * (f (croot a * x)) := by
      rw [mul_assoc]
      apply mul_nonneg <| le_of_lt hcroot
      apply mul_nonneg
      exact nonneg_of_nonneg <| le_of_lt hx
      apply nonneg_of_nonneg
      apply mul_nonneg <| le_of_lt hcroot
      exact le_of_lt hx
    have H2 := aux_sq_eq_sq H1 this
    have : croot a = a ^ ((3 : ℝ)⁻¹) := by
      unfold croot
      split
      apply congrArg
      norm_num
      linarith
    rw [this] at H2
    linear_combination -H2
  -- Prove if \(a, b \in S\), then \(a + b \in S\)
  have add_mem_S {a b} (ha : a ∈ S) (hb : b ∈ S) : a + b ∈ S := by
    simp [S]
    constructor; exact add_pos ha.1 hb.1
    intro x
    specialize h (croot a * croot x) (croot b * croot x)
    rw [mul_pow, aux_4188, aux_4188, mul_pow, aux_4188, aux_4188, ← add_mul] at h
    have hcroota := croot_mem_S ha
    have hcrootb := croot_mem_S hb
    rw [hcroota.2, hcrootb.2] at h
    have := hx0 (croot x)
    rw [aux_4188] at this
    rw [this, h]
    conv =>
      lhs
      congr
      rw [← add_mul]; rfl
      rw [mul_pow, mul_pow, sub_eq_add_neg]
      lhs; rhs; rhs
      rw [mul_assoc, mul_comm (f (croot x)), mul_assoc, ← pow_two, ← mul_assoc]
      rfl
    have : a+b=(croot a + croot b)*((croot a)^2 - croot a * croot b +(croot b)^2) := by
      conv_lhs => rw [← aux_4188 a, ← aux_4188 b]
      ring
    rw [this]
    ring
  -- Using induction, since \(1 \in S\), it implies \(1 + 1 = 2 \in S\), and by induction, any natural number \(a \in S\)
  have hS (n : ℕ) : ↑(n + 1) ∈ S := by
    induction' n with n ih
    . convert one_mem_S; norm_num
    convert add_mem_S ih one_mem_S; norm_num
  -- Specifically, \(1996 \in S\), implying:
  --  \[
  --  f(1996 x) = 1996 f(x)
  --  \]
  exact (hS 1995).2
