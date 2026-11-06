import Mathlib

/-Define the function $f(x)=\frac{b}{2x-3}$. If $f(2)=f^{-1}(b+1)$, find the product of all possible values of $b$.-/
theorem algebra_15435 {roots : Set ℝ} {f : ℝ → ℝ → ℝ} (hf: f = fun b x => b / (2 * x - 3)) (hr: roots = {b | (f b) (2) ∈ (f b) ⁻¹' {b + 1}}) :
      (roots = {(√7 + 1)/2,(-√7 + 1)/2}) ∧ (∏x∈{(√7 + 1)/2,(-√7 + 1)/2}, x) = -3/2 := by
  -- solve the equation `2 * x^2 - 2 * x - 3 = 0`
  have solve: ∀x, 2 * x^2 - 2 * x - 3 = 0 -> x = (√7 + 1)/2 ∨ x = (-√7 + 1)/2 := by
    intro x hx
    have : 2 * (x - (√7 + 1)/2) * (x - (-√7 + 1)/2) = 2 * x^2 - 2 * x - 3 := by
      field_simp
      ring_nf
      rw [Real.sq_sqrt]
      repeat linarith
    rw [this.symm] at hx
    simp at hx
    repeat rw [sub_eq_zero] at hx
    exact hx

  -- because linearith can't handle the properties of √7 correctly
  -- so we must give hints manually
  have : 2 < √7 := by
    rw [Real.lt_sqrt, pow_two]
    repeat linarith
  have : (1 + √7) * (1 - √7) = -6 := by
    rw [←Commute.mul_self_sub_mul_self_eq, ←pow_two, ←pow_two, Real.sq_sqrt]
    repeat linarith
    simp

  constructor
  . -- prove roots = {(√7 + 1)/2,(-√7 + 1)/2}
    apply Set.ext
    intro b
    have q : (2 * b - 3) * (b + 1) = (2 * b^2 - b - 3) := by linarith
    constructor
    . -- prove b ∈ roots → b ∈ {(√7 + 1) / 2, (-√7 + 1) / 2}
      intro hb
      rw [hr] at hb; simp at hb
      have : f b 2 = b := by rw [hf]; simp; ring_nf

      -- b / (2 * b - 3) = b + 1
      rw [this, hf] at hb; simp at hb

      by_cases h : b = 0
      . -- if b = 0, then f x ≡ 0, so we could not find any x that f x = 0 + 1 = 1
        rw [h] at hb
        field_simp at hb

      -- prove that b ≠ 3/2
      by_cases h: 2 * b - 3 = 0
      . have h: b = 3/2 := by linarith
        rw [h] at hb
        field_simp at hb
        linarith

      -- b / (2 * b - 3) = b + 1 => 2 * b^2 - 2 * b - 3 = 0 when 2 * b - 3 ≠ 0
      have (h : 2 * b - 3 ≠ 0) : 0 = (2 * b^2 - b - 3) - b := by rw [q.symm, hb.symm]; field_simp
      have equation : 2 * b^2 - 2 * b - 3 = 0 := by linarith [this h]
      exact solve b equation
    . -- prove b ∈ {(√7 + 1) / 2, (-√7 + 1) / 2} → b ∈ roots
      intro hb
      rw [hr]
      have p : 2 * 2 - 3 = (1 : ℝ) := by linarith
      rcases hb with r₁ | r₂
      . -- b = (√7 + 1)/2
        simp
        rw [hf]
        field_simp
        rw [p, mul_one, one_mul, div_eq_iff_mul_eq, mul_comm, q, r₁, div_pow, add_sq, Real.sq_sqrt]
        ring_nf
        repeat linarith

      . -- b = (-√7 + 1)/2
        simp
        rw [hf]
        field_simp
        rw [p, mul_one, one_mul, div_eq_iff_mul_eq, mul_comm, q, r₂, div_pow, add_sq, neg_pow_two, Real.sq_sqrt]
        ring_nf
        repeat linarith
        rw [r₂]
        field_simp
        linarith

  . -- prove ∏x∈{(√7 + 1)/2,(-√7 + 1)/2}, x = -3/2
    rw [Finset.prod_insert]
    repeat field_simp; repeat linarith
