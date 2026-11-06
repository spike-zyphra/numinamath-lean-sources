import Mathlib

open Real
open Set

/-
Prove that if x^y^k = y^x^k for positive integers x, y, and k > 1, then x = y
-/
theorem pow_eq (x y k:ℕ )(hx:x>0)(hy: y>0)(hk: k>1)(e: x^y^k=y^x^k): x=y:=by

  -- Case 1: x = 1
  by_cases u: x=1
  rw[u] at e
  rw[one_pow,one_pow,pow_one] at e
  rw[u]
  exact e

  -- Case 2: y = 1
  by_cases v: y=1
  rw[v] at e
  rw[one_pow,one_pow,pow_one] at e
  rw[v]
  exact e

  -- Now consider x ≥ 2, y ≥ 2, k ≥ 2
  have hx : x ≥ 2 := by omega
  have hy : y ≥ 2 := by omega
  have hk : k ≥ 2 := by omega

  -- Define the function f(x) = (log x)/x^k
  let f (x:ℝ ) : ℝ:= (log x)/x^k

  -- Lift the equality from naturals to reals
  have s: (x:ℝ)^(y:ℝ)^k=(y:ℝ)^(x:ℝ)^k:= by
    norm_cast

  -- Take the natural logarithm of both sides
  have t: log (x^(y:ℝ)^k)=log (y^(x:ℝ)^k) :=by
    rw[s]

  -- Apply logarithm rules
  rw[log_rpow] at t
  rw[log_rpow] at t

  -- Show that f(x) = f(y)
  have u: f (x:ℝ)=f (y:ℝ):=by
    dsimp only [f]
    field_simp
    rw[mul_comm]
    symm
    rw[mul_comm]
    symm
    exact t

  -- Compute the derivative of f
  have deriv_f : ∀ z≥2, HasDerivAt (f) ((1 - k * log z) / (z ^ ((k:ℝ) + 1))) z := by
    intro z
    intro hz
    rw[ge_iff_le] at hz
    have v: z≠0:= by
      by_contra con
      rw[con] at hz
      linarith

    have l: 1/z=z⁻¹ := by
      symm
      rw[inv_eq_one_div]
    have deriv_log : HasDerivAt log (1/z) z := by
      rw[l]
      exact hasDerivAt_log v

    have deriv_pow : HasDerivAt (fun x => x ^ (k : ℝ)) (k * z ^ ((k:ℝ) - 1)) z := by
      have h : z ≠ 0 ∨ 1 ≤ (k:ℝ) := Or.inl v
      exact hasDerivAt_rpow_const h
    have r:z≠0:= by linarith

    have rr: z ^ ↑k ≠ 0:= by
      by_contra g
      rw[ pow_eq_zero_iff'] at g
      obtain ⟨p,q⟩ :=g
      contradiction

    convert HasDerivAt.div deriv_log deriv_pow
    field_simp
    dsimp only [f]
    symm
    rw[mul_comm,mul_assoc]

    apply Iff.of_eq
    congr! 1
    field_simp

    have n : z ^ k - log z * (k * z ^ ((k:ℝ) - (1:ℝ)) * z) = z ^ k - k * log z * z ^ k := by
      rw [← mul_assoc,← Real.rpow_natCast,mul_assoc,mul_assoc]
      field_simp
      rw [←mul_assoc,mul_comm (log z)]
      simp
      left
      rw[←rpow_add_one,sub_add_cancel]
      exact rpow_natCast z k
      exact v

    rw[n]

    have q: (z ^ k - k * log z * z ^ k) =(1 - k * log z ) *z^k:= by
      nth_rw 1 [←one_mul (z ^ k)]
      rw[←sub_mul]
    rw[q]
    rw[mul_assoc]
    simp
    left
    rw[←pow_mul]
    rw[Real.rpow_add,rpow_one,mul_comm,mul_two,pow_add,←mul_assoc]
    simp
    left
    rw[mul_comm]
    linarith

  -- Show that the numerator of the derivative is negative for z ≥ 2
  have ne: ∀ z≥2,1 - ↑k * log z < 0:=by
    simp
    intro z
    intro zg
    have hlog : 2*log z ≥  2*log 2 := by
      simp
      apply Real.log_le_log
      linarith
      exact zg
    have ge: ↑k * log z≥ 2*log z:=by
      gcongr
      have hlog2_pos : log 2 > 0 := by
        apply Real.log_pos
        norm_num
      linarith
      apply Nat.cast_le.mpr hk
    have Ge: ↑k * log z≥2*log 2:= by linarith
    have uu: 2 * log 2>1:=by
      have :=log_two_gt_d9
      linarith
    linarith

  -- Show that the denominator of the derivative is positive for z ≥ 2
  have po: ∀ z≥2,(0:ℝ )<z ^ (↑k + 1) := by
    intro
    intro zg
    apply pow_pos
    have r:2>0:=by norm_num
    linarith

  -- Combine the above results to show the derivative is negative for z ≥ 2
  have n: ∀ z≥2,(1 - ↑k * log z) / z ^ ((k:ℝ) + 1)<0:= by
    intro z
    intro zg
    apply div_neg_of_neg_of_pos
    apply ne
    exact zg
    norm_cast
    apply po
    exact zg

  swap
  norm_cast
  swap
  norm_cast

  -- Prove that f is strictly decreasing on [2, ∞)
  have f_strict_mono : StrictAntiOn f (Set.Ici 2) := by
    intro x hx y hy hxy
    have hdiff : DifferentiableOn ℝ f (Ioo x y) := by
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      have hz' : 2 ≤ z := by
        apply le_trans hx (le_of_lt hz.1)
      exact (deriv_f z hz').differentiableAt

    have hxy' : Icc x y ⊆ Ici 2 := by
      intro z hz
      rcases hz with ⟨hxz, hzy⟩
      exact le_trans hx hxz

    have hf_cont: ContinuousOn f (Icc x y) :=by
      apply ContinuousOn.div
      have X: x≥ 2:= hx
      have X: x≥ 0:= by linarith
      apply continuousOn_log.mono
      intros t ht
      have ht_ge_2 : t ≥ 2 := hxy' ht
      show t ≠ 0
      linarith

      swap
      intro r hr rz
      simp at rz
      obtain⟨r1,r2⟩ :=hr
      obtain⟨r3,r4⟩ :=rz
      have X:x≥ 2:=hx
      linarith

      apply (continuousOn_pow k).mono hxy'

    -- Apply the Mean Value Theorem
    have Z: ∃ c ∈ Ioo x y, deriv f c = (f y - f x) / (y - x):=by
      apply exists_deriv_eq_slope f hxy hf_cont hdiff

    obtain ⟨c, hc_mem, hc_slope⟩ :=Z
    have hc_lt : x < c ∧ c < y := by simpa [mem_Ioo] using hc_mem
    have hx : 2 ≤ x  := by simpa [mem_Ici] using hx
    obtain ⟨hc,hc'⟩  :=hc_lt
    have hc: 2<c:= by linarith
    have dc: deriv f c<0:= by
      have h_has_deriv : HasDerivAt f ((1 - k * log c) / c^((k:ℝ) + 1)) c := by
        apply deriv_f c
        linarith [hc]
      have h_deriv : deriv f c = (1 - (k : ℝ) * log c) / c ^ ((k:ℝ) + 1) :=
        h_has_deriv.deriv
      rw [h_deriv]
      apply n
      linarith
    have G : (f y - f x) / (y - x) <0:=by linarith
    have y_sub_x_pos : y - x > 0 := by linarith
    apply div_neg_iff.mp at G
    obtain G1|G2 :=G
    obtain ⟨G3,G4⟩  :=G1
    linarith
    obtain ⟨G3,G4⟩  :=G2
    linarith

  -- Show that x and y are in the domain where f is strictly decreasing
  have hx' : (x : ℝ) ∈ Set.Ici 2 := by simp [hx]
  have hy' : (y : ℝ) ∈ Set.Ici 2 := by simp [hy]

  -- Case 1: x < y leads to contradiction
  by_cases ge:(x:ℝ)< (y:ℝ)
  have T:=f_strict_mono hx' hy' ge
  rw[u] at T
  apply lt_irrefl at T
  exact  False.elim T

  -- Case 2: y < x leads to contradiction
  by_cases r:(y:ℝ)< (x:ℝ)
  have T:=f_strict_mono hy' hx' r
  rw[u] at T
  apply lt_irrefl at T
  exact  False.elim T

  -- Therefore, x = y
  simp at ge
  simp at r
  exact le_antisymm r ge
