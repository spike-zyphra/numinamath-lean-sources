import Mathlib

open Real Finset
open scoped BigOperators Polynomial

/- Example 6 For $n \in \mathbf{N}^{*}, n \geqslant 2$, prove the following identities:
(1) $\prod_{k=1}^{n-1}\left|\cos \frac{k \pi}{n}\right|-\left(\frac{1}{2}\right)^{n}\left[1-(-1)^{n}\right]$;
(2) $\prod_{k=1}^{n-1} \sin \frac{k \pi}{n}=n \cdot\left(\frac{1}{2}\right)^{n-1}$. -/
theorem algebra_291167 {n : ℕ} (hn : 2 ≤ n) :
    ∏ k ∈ Icc 1 (n - 1), abs (cos (k * π / n)) -
    (1 / 2) ^ n * (1 - (-1) ^ n) =
    0 ∧
    ∏ k ∈ Icc 1 (n - 1), sin (k * π / n) =
    n * (1 / 2) ^ (n - 1) := by
  -- define e(k) = exp(2 * π * I * (k / n))
  set e : ℕ → ℂ := fun i => Complex.exp (2 * π * Complex.I * (i / n))
  -- show that ∑ i ∈ [0, n), x ^ i = ∏ i ∈ [1, n - 1], (x - e i)
  have h (x : ℂ) : ∑ i ∈ range n, x ^ i = ∏ i ∈ Icc 1 (n - 1), (x - e i) := by
    -- values of e(k) for k ∈ [0, n) are complex nth-roots of unity
    -- so they are also all roots of the complex polynomial X^n - 1
    have nthRootsFinset_complex : Polynomial.nthRootsFinset n ℂ = (range n).image e := by
      replace hn : 0 < n := by omega
      have hn0 : NeZero n := NeZero.of_pos (by omega)
      ext z
      simp only [mem_image, mem_range, Polynomial.mem_nthRootsFinset hn]
      -- we need to show that z^n = 1 ↔ e k = z for some k < n
      constructor
      · intro h
        -- if we have z^n = 1 then z is a unit in ℂ and z ∈ rootsOfUnity n ℂ
        have u : IsUnit z := by
          apply Ne.isUnit
          contrapose! h
          simp [h, zero_pow (show n ≠ 0 by omega)]
        have : u.unit ∈ rootsOfUnity n ℂ := by
          rw [mem_rootsOfUnity']
          simp [h]
        -- a root of unity in ℂ is equal to some e(k) with k < n
        rw [Complex.mem_rootsOfUnity] at this
        have ⟨i, hi⟩ := this
        use i, hi.1
        simp [hi.2, e]
      · intro ⟨i, hi⟩
        -- it is easy to show that e(k)^n = 1
        rw [←hi.2, ←Complex.exp_nat_mul, Complex.exp_eq_one_iff]
        use i
        field_simp [show (n : ℂ) ≠ 0 by norm_cast; omega]
        ring
    have e_inj : Set.InjOn e (range n) := by
      apply Finset.injOn_of_card_image_eq
      rw [←nthRootsFinset_complex, card_range, IsPrimitiveRoot.card_nthRootsFinset (Complex.isPrimitiveRoot_exp n (by omega))]
    -- define p = (X^(n - 1) + X^(n - 2) + ... + X + 1) * (X - 1)
    set p : ℂ[X] := (∑ i ∈ range n, Polynomial.X ^ i) * (Polynomial.X - 1)
    -- define q = (X - e 0) * (X - e 1) * ... * (X - e (n - 1))
    set q : ℂ[X] := ∏ i ∈ range n, (Polynomial.X - Polynomial.C (Complex.exp (2 * π * Complex.I * (i / n))))
    replace hn : 0 < n := by omega
    -- it is enough to show that p = q
    suffices eq : p = q by
      -- suppose that p = q
      simp [p, q, Finset.prod_range_eq_mul_Ico _ hn] at eq
      have : (Polynomial.X - 1 : ℂ[X]) ≠ 0 := by apply Polynomial.X_sub_C_ne_zero
      -- cancel (X - 1) and get (X^(n - 1) + X^(n - 2) + ... + X + 1) = (X - e 1) * ... * (X - e (n - 1))
      rw [mul_comm, mul_right_inj' this] at eq
      -- evaluate both polynomials at x and get the required equality
      apply_fun (Polynomial.eval x) at eq
      simp [Polynomial.eval_prod] at eq
      rw [eq]
      exact prod_congr rfl (fun i hi => rfl)
    -- we have p = X ^ n - 1
    simp [p, geom_sum_mul]
    -- we proved that all roots of p = X ^ n - 1 are e 0, e 1, ... e (n - 1)
    rw [Polynomial.X_pow_sub_one_eq_prod hn (Complex.isPrimitiveRoot_exp n (by omega))]
    -- so p can be written as a product (X - e 0) * (X - e 1) * ... * (X - e (n - 1)) = q
    simp [nthRootsFinset_complex, q]
    rw [Finset.prod_image e_inj]
  constructor
  -- prove the first identity from the theorem statement
  -- set x = -1 in h
  · specialize h (-1)
    -- we get ∑ i ∈ [0, n) (-1)^i = (1 - (-1) ^ n) / 2
    rw [neg_one_geom_sum] at h
    have eq1 : ‖if Even n then 0 else (1 : ℂ)‖ = (1 - (-1) ^ n) / 2 := by
      split_ifs with h <;> simp
      · simp [h.neg_one_pow]
      · simp [Odd.neg_one_pow (Nat.not_even_iff_odd.mp h)]
    -- show that 1 + e i = 2 * cos (π * (i / n)) * exp (π * I * (i / n))
    have eq2 i : 1 + e i = 2 * Complex.cos (π * (i / n)) * Complex.exp (π * Complex.I * (i / n)) := by
      simp_rw [Complex.two_cos, e]
      ring_nf
      simp [←Complex.exp_add, ←Complex.exp_nat_mul]
      congr 1
      ring
    -- it follows that ‖-1 - e i‖ = 2 * |cos (π * (i / n))|
    have eq3 i : ‖-1 - e i‖ = 2 * |Real.cos (i * π / n)| := by
      rw [show -1 - e i = -(1 + e i) by ring, norm_neg, eq2]
      simp_rw [norm_mul]
      rw [show (π * (i / n) : ℂ) = ((i * (π / n) : ℝ) : ℂ) by push_cast; ring, ←Complex.ofReal_cos]
      rw [show ↑π * Complex.I * (↑i / ↑n) = (π * (i / n) : ℝ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
      simp_rw [Complex.norm_eq_abs, Complex.abs_ofReal]
      simp [mul_div]
    -- apply the complex norm at h
    apply_fun (‖·‖) at h
    -- we get (1 - (-1)^n) / 2 = 2^(n - 1) * ∏ i ∈ [1, n - 1], |cos (i * π / n)|
    simp [eq1, eq3, ←Finset.pow_card_mul_prod] at h
    -- the result follows with some algebraic simplifications
    field_simp at h ⊢
    rw [h]
    have : ∀ x : ℝ, (2 ^ (n - 1) * x) * 2 = x * 2 ^ n := by
      intro x
      rw [show (2 ^ (n - 1) * x) * 2 = x * (2 ^ (n - 1) * 2) by ring]
      nth_rw 2 [show n = (n - 1) + 1 by omega]
      rw [pow_add, pow_one]
    simp [this]
  -- prove the second identity from the theorem statement
  -- set x = 1 in h
  · specialize h 1
    -- apply the complex norm at h
    apply_fun (‖·‖) at h
    simp at h
    nth_rw 2 [h]
    nth_rw 3 [show n - 1 = (Icc 1 (n - 1)).card by simp]
    rw [Finset.prod_mul_pow_card]
    apply Finset.prod_congr rfl
    intro i hi
    -- show that 1 - e i = -I * exp (π * I * (i / n)) * (2 * sin (π * (i / n)))
    have eq : 1 - e i = -Complex.I * (Complex.exp (π * Complex.I * (i / n)) * (2 * Complex.sin (π * (i / n)))) := by
      simp_rw [Complex.two_sin, e]
      ring_nf
      simp [Complex.I_sq, neg_mul, one_mul, neg_neg, ←Complex.exp_add, ←Complex.exp_nat_mul]
      congr 2
      ring
    simp [eq]
    have habs (z : ℂ) : z.abs = ‖z‖ := rfl
    rw [show ↑π * Complex.I * (↑i / ↑n) = (π * (i / n) : ℝ) * Complex.I by push_cast; ring]
    rw [habs, Complex.norm_exp_ofReal_mul_I]
    rw [show (π * (i / n) : ℂ) = ((i * (π / n) : ℝ) : ℂ) by push_cast; ring, ←Complex.ofReal_sin]
    -- it is left to prove sin (i * π / n) = |sin (i * π / n)|
    -- it is enought to show that 0 ≤ sin (i * π / n) for i ∈ [1, n - 1]
    have hsin : 0 ≤ sin (i * (π / n)) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · rw [mul_div]
        apply div_le_of_le_mul₀ (by positivity) (by positivity)
        rw [mul_comm]
        apply mul_le_mul (le_refl _) _ (by positivity) (by positivity)
        norm_cast
        simp at hi
        omega
    rw [Complex.abs_of_nonneg hsin]
    ring_nf