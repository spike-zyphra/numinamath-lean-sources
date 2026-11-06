import Mathlib

/- 4. For what values of the parameter $a$ does the system of equations


$$

\left\{\begin{array}{l}
x^{2}+y^{2}+z^{2}+4 y=0 \\
x+a y+a z-a=0
\end{array}\right.

$$


have a unique solution -/

-- unique existance of any property in ℝ × ℝ × ℝ and WithLp 2 (Fin 3 → ℝ) are equivalent
lemma l_equiv_geo (P : ℝ → ℝ → ℝ → Prop) : (∃! (p : ℝ × ℝ × ℝ), P p.1 p.2.1 p.2.2) ↔
    (∃! (p : WithLp 2 (Fin 3 → ℝ)), P (p 0) (p 1) (p 2)) := by
  constructor <;> rintro ⟨p, hp, hp'⟩
  . let q (i : Fin 3) := match i with
    | 0 => p.1
    | 1 => p.2.1
    | 2 => p.2.2
    use q
    simp [q, hp]
    rintro q' hq'
    specialize hp' ⟨q' 0, q' 1, q' 2⟩  hq'
    repeat rw [Prod.ext_iff] at hp'
    simp at hp'
    ext i
    match i with
    | 0 => simpa using hp'.left
    | 1 => simpa using hp'.right.left
    | 2 => simpa using hp'.right.right
  . let q : ℝ × ℝ × ℝ := ⟨p 0, p 1, p 2⟩
    use q
    simp [q, hp]
    rintro a b c habc
    specialize hp' (fun i => match i with |0 => a | 1 => b | 2 => c) habc
    rw [← hp']
    simp

-- the first equaiton states taht p is on sphere of radius 2 with center (0, -2, 0)
lemma l_sphere (p : WithLp 2 (Fin 3 → ℝ)) : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + 4 * p 1 = 0 ↔ ‖p - !₂[0, -2, 0]‖ ^ 2 = 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  have : p - !₂[0, -2, 0] = !₂[p 0, p 1 + 2, p 2] := by
    ext i
    fin_cases i <;> simp
  rw [this, Fin.sum_univ_three, Real.sq_sqrt (by positivity)]
  simp
  constructor <;> (rintro h; linarith)

-- the second equation states that p is in plane with normal (1, a, a) and dot product a
lemma l_plane (p : WithLp 2 (Fin 3 → ℝ)) : p 0 + a * p 1 + a * p 2 - a = 0 ↔ inner p !₂[1, a, a] = a := by
  simp [Fin.sum_univ_three]
  constructor <;> (rintro h; linarith)

-- squared distance to any point is composed of projection on a vector and the orthogonal part
lemma l_distance {p c n : WithLp 2 (Fin 3 → ℝ)} (hn : n ≠ 0)  :
    ‖p - c‖^2 = ‖(inner n (p - c) / ‖n‖^2) • n‖^2 + ‖(p - c) - (inner n (p - c) / ‖n‖^2) • n‖^2 := by
  nth_rw 2 [sq]; nth_rw 4 [sq]
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_real]
  . rw [← sq]
    congr
    simp
  . rw [inner_sub_right, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
    ring_nf
    rw [mul_assoc]
    have : ‖n‖ ≠ 0 := by simpa
    conv_lhs => arg 1; arg 1; arg 2; equals ‖n‖⁻¹ ^ 2 => field_simp; ring
    ring

-- unique point belongs to plane and sphere if and only if distance to plane from center is radius
lemma l_uniq_soln {r v : ℝ} {c n m : WithLp 2 (Fin 3 → ℝ)} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : inner n m = (0 : ℝ)) :
    (∃! p, ‖p - c‖ ^ 2 = r ^ 2 ∧ inner p n = v) ↔ ‖v - inner c n‖^2 / ‖n‖^2 = r^2 := by
  apply not_iff_not.mp
  obtain h | h | h := lt_trichotomy (‖v - inner c n‖^2 / ‖n‖^2) (r^2)
  -- if distance to plane is less than r, then there are multiple solutions
  . simp only [h.ne, not_false_eq_true, iff_true]
    apply mt ExistsUnique.unique
    push_neg
    let s := (v - inner c n) / ‖n‖
    have hs' : 0 < √(r ^ 2 - s ^ 2) := by
      simp
      convert h
      rw [Real.norm_eq_abs, sq_abs, div_pow]
    have hs : √(r^2 - s^2) ^ 2 = r^2 - s^2 := by
      simp at hs'
      rw [Real.sq_sqrt (by linarith)]
    have h_perp : inner ((s / ‖n‖) • n) ((√(r^2 - s^2) / ‖m‖) • m) = (0 : ℝ) := by
      rw [real_inner_smul_left, real_inner_smul_right, hnm]
      simp
    -- the solutions are made by n and it's perpendicular vecotr m, mainly _ * n + _ * m and _ * n - _ * m
    use c + (s / ‖n‖) • n +  (√(r^2 - s^2) / ‖m‖) • m, c + (s / ‖n‖) • n -  (√(r^2 - s^2) / ‖m‖) • m
    and_intros
    -- first point belongs to sphere
    . rw [add_comm, add_comm c, ← add_sub, ← add_sub _ _ c]
      simp
      rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_real (by rwa [real_inner_comm]), ← sq, ← sq]
      rw [norm_smul, norm_smul]
      simp
      field_simp
      rw [hs]
      ring
    -- first point belongs to plane
    . rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_comm n m, hnm]
      simp only [mul_zero, add_zero, s]
      rw [real_inner_self_eq_norm_sq]
      conv_lhs => arg 2; equals (v - inner c n) => field_simp; left; ring
      ring
    -- second point belongs to sphere
    . rw [add_comm, ← add_sub, ← add_sub]
      simp
      rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_real (by simp [inner_neg_right, h_perp]), ← sq, ← sq]
      rw [norm_smul, norm_neg, norm_smul]
      simp
      field_simp
      rw [hs]
      ring
    -- second point belongs to plane
    . rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_comm n m, hnm]
      simp only [mul_zero, sub_zero, s]
      rw [real_inner_self_eq_norm_sq]
      conv_lhs => arg 2; equals (v - inner c n) => field_simp; left; ring
      ring
    -- both point are different
    . nth_rw 2 [sub_eq_add_neg]
      simp
      by_contra h'
      rw [← add_eq_zero_iff_eq_neg, ← add_smul, smul_eq_zero_iff_left hm, ← two_mul] at h'
      have : 0 < 2 * (√(r ^ 2 - s ^ 2) / ‖m‖) := by positivity
      linarith
  -- if distance is exactly r, then there is unique solution whic is distance * n / ‖n‖
  . suffices ∃! p, ‖p - c‖ ^ 2 = r ^ 2 ∧ inner p n = v by
      simp only [this, h]
    use c + ((v - inner c n) / ‖n‖ ^ 2) • n
    and_intros
    -- point belongs to sphere
    . rw [add_sub_cancel_left, norm_smul, mul_pow, norm_div, div_pow, norm_pow, norm_norm]
      convert h using 1
      field_simp
      ring
    -- point belongs to plane
    . rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      conv_lhs => arg 2; equals (v - inner c n) => field_simp
      simp
    -- any other solution is also the point as the orthogonal part of distance is 0
    . rintro q ⟨hq1, hq2⟩
      rw [l_distance hn, inner_sub_right, real_inner_comm, hq2, norm_smul, norm_div, norm_pow, norm_norm] at hq1
      conv_lhs at hq1 => arg 1; arg 1; equals ‖v - inner n c‖ / ‖n‖ => field_simp; ring
      rw [div_pow, real_inner_comm, h] at hq1
      replace hq1 : ‖q - c - ((v - inner c n) / ‖n‖ ^ 2) • n‖ ^ 2 = 0 := by linarith
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at hq1
      rw [sub_eq_zero] at hq1
      rw [← hq1]
      simp
  -- if distance is greater than r then there are no solution
  . simp only [h.ne.symm, not_false_eq_true, iff_true]
    apply mt ExistsUnique.exists
    simp_rw [and_comm]
    push_neg
    rintro p hp
    rw [l_distance hn, inner_sub_right, real_inner_comm p n, hp]
    suffices r^2 < ‖((v - inner n c) / ‖n‖ ^ 2) • n‖ ^ 2 by
      have : 0 ≤ ‖p - c - ((v - inner n c) / ‖n‖ ^ 2) • n‖ ^ 2 := by positivity
      linarith
    rw [norm_smul, norm_div, norm_pow, norm_norm]
    conv_rhs => arg 1; equals ‖v - inner n c‖ / ‖n‖ => field_simp; ring
    rw [div_pow]
    convert h using 4
    rw [real_inner_comm]

theorem algebra_178196 (a : ℝ) :
    (∃! p : ℝ × ℝ × ℝ, (fun x y z => x^2 + y^2 + z^2 + 4 * y = 0 ∧ x + a * y + a * z - a = 0)
    p.1 p.2.1 p.2.2) ↔ a = 2 ∨ a = -2 := by
  -- we first convert to WithLp 2 (Fin 3 → ℝ), then convert it to distance formulation
  rw [l_equiv_geo (fun x y z => x^2 + y^2 + z^2 + 4 * y = 0 ∧ x + a * y + a * z - a = 0)]
  simp_rw [l_sphere, l_plane]
  have hn : !₂[1, a, a] ≠ 0 := by
    apply mt congrFun
    simp; use 0; simp
  have hm : !₂[a, -1, 0] ≠ 0 := by
    apply mt congrFun
    simp; use 1; simp
  have hnm : inner (!₂[1, a, a]) (!₂[a, -1, 0]) = (0 : ℝ) := by
    simp [Fin.sum_univ_three]
  rw [l_uniq_soln hn hm hnm]
  -- now the condition becmes a^2 = 2^2, then obvious
  simp [Fin.sum_univ_three, PiLp.norm_sq_eq_of_L2]
  ring_nf
  field_simp [show 1 + a ^ 2 * 2 ≠ 0 by positivity]
  ring_nf
  constructor <;> rintro h
  . replace h : a^2 = 2^2 := by linarith
    rw [pow_eq_pow_iff_of_ne_zero (by norm_num)] at h
    simpa [show Even 2 by decide] using h
  . obtain rfl | rfl := h <;> norm_num