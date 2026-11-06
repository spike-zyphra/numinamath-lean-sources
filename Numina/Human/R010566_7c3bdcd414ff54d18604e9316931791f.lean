import Mathlib

open Real Set

set_option maxHeartbeats 500000
/- Find the number of solutions to $\cos \frac{x}{4} = \cos x$ in the interval $0 < x < 24 \pi.$ -/
theorem calculus_22492:
  {x:ℝ | x ∈ Ioo 0 (24 * π) ∧ cos (x/4) = cos x}.encard = 20 := by
  -- cos x/4 = cos x, so cos x - cos x/4 = 0
  have h1 (x:ℝ): cos (x/4) = cos x ↔ cos x - cos (x/4) = 0 := by
    constructor <;> intro h <;> linarith [h]
  -- by sum-to-product, cos a - cos b = 2sin((a-b)/2)sin((a+b)/2)
  have sum_to_product(a b:ℝ): cos a - cos b =
    -2*(sin ((a-b)/2) * sin ((a+b)/2)) := by
    have hh1: a = (a-b)/2 + (a+b)/2 := by ring
    have hh2: b = (a+b)/2 - (a-b)/2 := by ring
    nth_rw 1 [hh1]
    nth_rw 3 [hh2]
    rw [cos_add, cos_sub]; ring
  -- so we can solve cos x - cos (x/4) = 0, sin (5x/8) = 0 or sin (3x/8) = 0
  have h2 (x:ℝ): cos (x/4) = cos x ↔ (sin (5*x/8) = 0 ∨ sin (3*x/8) = 0) := by
    rw [h1, sum_to_product x (x/4), mul_eq_zero]; simp
    have hh1: (x - x/4)/2 = 3*x/8 := by ring
    have hh2: (x+x/4)/2 = 5*x/8 := by ring
    rw [hh1, hh2]
    rw [or_comm]
  -- if sin x = 0, then x = kπ. so x = 8/5 kπ or 8/3 kπ
  have h3: {x:ℝ | x ∈ Ioo 0 (24 * π) ∧ cos (x/4) = cos x} =
    {x:ℝ | x ∈ Ioo 0 (24 * π) ∧ ∃ n:ℤ, x = (8/5)*n*π ∨ x = (8/3)*n*π}
    := by
    ext x; simp; intro xlb _
    rw [h2 x, sin_eq_zero_iff, sin_eq_zero_iff]
    constructor <;> intro h
    · rcases h with hh | hh <;> rcases hh with ⟨m,hm⟩
      <;> use m <;> rw [mul_assoc, mul_assoc, hm]
      · left; linarith
      · right; linarith
    · rcases h with ⟨m,hm⟩
      have mnonneg: 0 ≤ m := by
        rcases hm with hh | hh <;> rw [hh] at xlb
        · have tt1: 0 < (8/5:ℝ) := by norm_num
          by_contra! hc
          have hc': (m:ℝ) < 0 := by
            exact Int.cast_lt_zero.mpr hc
          have tt2: (8/5:ℝ) * m < 0 := by
            linarith [tt1, hc']
          have tt3: 8/5 * m * π < 0 := by
            apply mul_neg_of_neg_of_pos tt2 pi_pos
          linarith [tt3, xlb]
        · have tt1: 0 < (8/3:ℝ) := by norm_num
          by_contra! hc
          have hc': (m:ℝ) < 0 := by
            exact Int.cast_lt_zero.mpr hc
          have tt2: (8/3:ℝ) * m < 0 := by
            linarith [tt1, hc']
          have tt3: 8/3 * m * π < 0 := by
            apply mul_neg_of_neg_of_pos tt2 pi_pos
          linarith [tt3, xlb]
      have mn: m.toNat = m := Int.toNat_of_nonneg mnonneg
      rcases hm with hh | hh <;> rw [hh]
      · left; use m.toNat; rw [mn]; ring
      · right; use m.toNat; rw [mn]; ring
  -- 24 = 120/5, 8,15,...,112, 14 numbers have the form 8*k.
  have h4(x:ℝ)(m:ℤ)(hlb: 0 < x)(hub: x < 24*π)(hm: x = 8 / 5 * ↑m * π):
    0 < m ∧ m < 15 := by
    rw [hm] at hlb hub
    have tt1: 0 < (8/5:ℝ) := by norm_num
    constructor
    · by_contra! hc
      have hc': (m:ℝ) ≤ 0 := by
        exact Int.cast_nonpos.mpr hc
      have tt2: (8/5:ℝ)*m ≤ 0 := by
        linarith [hc', tt1]
      have tt3: (8/5:ℝ)*m*π ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg tt2 pi_nonneg
      linarith [tt3, hlb]
    · by_contra! hc
      have hc': 15 ≤ (m:ℝ) := by
        apply Int.cast_le.mpr hc
      have: 24*π ≤ x := by
        rw [hm]
        have tt2: (8/5:ℝ)*15 ≤ 8/5*m := by
          exact (mul_le_mul_iff_of_pos_left tt1).mpr hc'
        have tt3: (8/5:ℝ)*15 = 24 := by ring
        rw [tt3] at tt2
        apply mul_le_mul tt2 (le_refl π) pi_nonneg (by linarith)
      rw [← hm] at hub; linarith [hub, this]
  -- and 24 = 72/3, 8,16,...,64, 8 numbers have the form 8*k.
  have h5(x:ℝ)(m:ℤ)(hlb: 0 < x)(hub: x < 24*π)(hm: x = 8 / 3 * ↑m * π):
    0 < m ∧ m < 9 := by
    rw [hm] at hlb hub
    have tt1: 0 < (8/3:ℝ) := by norm_num
    constructor
    · by_contra! hc
      have hc': (m:ℝ) ≤ 0 := by
        exact Int.cast_nonpos.mpr hc
      have tt2: (8/3:ℝ)*m ≤ 0 := by
        linarith [hc', tt1]
      have tt3: (8/3:ℝ)*m*π ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg tt2 pi_nonneg
      linarith [tt3, hlb]
    · by_contra! hc
      have hc': 9 ≤ (m:ℝ) := by
        apply Int.cast_le.mpr hc
      have: 24*π ≤ x := by
        rw [hm]
        have tt2: (8/3:ℝ)*9 ≤ 8/3*m := by
          exact (mul_le_mul_iff_of_pos_left tt1).mpr hc'
        have tt3: (8/3:ℝ)*9 = 24 := by ring
        rw [tt3] at tt2
        apply mul_le_mul tt2 (le_refl π) pi_nonneg (by linarith)
      rw [← hm] at hub; linarith [hub, this]
  let s := {x:ℝ | x ∈ Ioo 0 (24 * π) ∧ ∃ n:ℤ,x = (8/5)*n*π}
  let t := {x:ℝ | x ∈ Ioo 0 (24 * π) ∧ ∃ n:ℤ,x = (8/3)*n*π}
  have s_def: s = {x:ℝ | x ∈ Ioo 0 (24 * π) ∧ ∃ n:ℤ,x = (8/5)*n*π} := rfl
  have t_def: t = {x:ℝ | x ∈ Ioo 0 (24 * π) ∧ ∃ n:ℤ,x = (8/3)*n*π} := rfl
  have hsc': s.ncard = 14 := by
    let u: Set ℝ := {1,2,3,4,5,6,7,8,9,10,11,12,13,14}
    have u_def: u = {1,2,3,4,5,6,7,8,9,10,11,12,13,14} := rfl
    have: u.ncard = 14 := by
      rw [u_def]; rw [Set.ncard, Set.encard]; simp
    rw [← this]
    let f: (a: ℝ) → a ∈ s → ℝ := fun a (ha: a ∈ s) => (a/(8/5 * π))
    have f_def: f = fun a (ha: a ∈ s) => (a/(8/5 * π)) := rfl
    apply Set.ncard_congr f
    · intro a ha
      rw [f_def]; simp;
      rw [s_def] at ha; simp at ha
      rcases ha.right with ⟨m,hm⟩
      rw [hm]; ring_nf; field_simp
      have ⟨mlb,mub⟩ := h4 a m ha.left.left ha.left.right hm
      rw [u_def]
      simp
      interval_cases m <;> simp
    · intro a b ha hb hf
      rw [f_def] at hf; simp at hf
      have: (8/5*π) ≠ 0 := by
        have tt1: π ≠ 0 := by linarith [pi_pos]
        have tt2: (8/5:ℝ) ≠ 0 := by norm_num
        exact mul_ne_zero tt2 tt1
      field_simp [this] at hf; exact hf
    · intro b hb
      use (8/5*b*π)
      have: 8/5*b*π ∈ s := by
        rw [s_def]; simp
        rw [u_def] at hb; simp at hb
        constructor
        · rcases hb with bb | bb | bb | bb | bb | bb | bb | bb
            | bb | bb | bb | bb | bb | bb
          <;> rw [bb] <;> field_simp [pi_pos]
          <;> ring_nf <;> linarith [pi_pos]
        · use ⌊b⌋; simp [pi_pos.ne']
          rcases hb with bb | bb | bb | bb | bb | bb | bb | bb
            | bb | bb | bb | bb | bb | bb
          <;> rw [bb] <;> norm_num
      use this
      rw [f_def]; simp
      rw [mul_comm (8/5) b, mul_assoc]
      have: 8/5 * π ≠ 0 := by
        apply mul_ne_zero (by norm_num) pi_pos.ne'
      simp [this]
  have hsc: s.encard = 14 := by
    have: s.encard = s.ncard := by
      refine (ENat.toNat_eq_iff ?hn).mp rfl
      rw [hsc']; simp
    rw [this, hsc']; simp
  have htc': t.ncard = 8 := by
    let u: Set ℝ := {1,2,3,4,5,6,7,8}
    have u_def: u = {1,2,3,4,5,6,7,8} := rfl
    have: u.ncard = 8 := by
      rw [u_def]; rw [Set.ncard, Set.encard]; simp
    rw [← this]
    let f: (a: ℝ) → a ∈ t → ℝ := fun a (ha: a ∈ t) => (a/(8/3 * π))
    have f_def: f = fun a (ha: a ∈ t) => (a/(8/3 * π)) := rfl
    apply Set.ncard_congr f
    · intro a ha
      rw [f_def]; simp;
      rw [t_def] at ha; simp at ha
      rcases ha.right with ⟨m,hm⟩
      rw [hm]; ring_nf; field_simp
      have ⟨mlb,mub⟩ := h5 a m ha.left.left ha.left.right hm
      rw [u_def]
      simp
      interval_cases m <;> simp
    · intro a b ha hb hf
      rw [f_def] at hf; simp at hf
      have: (8/3*π) ≠ 0 := by
        have tt1: π ≠ 0 := by linarith [pi_pos]
        have tt2: (8/3:ℝ) ≠ 0 := by norm_num
        exact mul_ne_zero tt2 tt1
      field_simp [this] at hf; exact hf
    · intro b hb
      use (8/3*b*π)
      have: 8/3*b*π ∈ t := by
        rw [t_def]; simp
        rw [u_def] at hb; simp at hb
        constructor
        · rcases hb with bb | bb | bb | bb | bb | bb | bb | bb
          <;> rw [bb] <;> field_simp [pi_pos]
          <;> ring_nf <;> linarith [pi_pos]
        · use ⌊b⌋; simp [pi_pos.ne']
          rcases hb with bb | bb | bb | bb | bb | bb | bb | bb
          <;> rw [bb] <;> norm_num
      use this
      rw [f_def]; simp
      rw [mul_comm (8/3) b, mul_assoc]
      have: 8/3 * π ≠ 0 := by
        apply mul_ne_zero (by norm_num) pi_pos.ne'
      simp [this]
  have htc: t.encard = 8 := by
    have: t.encard = t.ncard := by
      have: t.ncard ≠ 0 := by
        rw [htc']; simp
      exact (ENat.toNat_eq_iff this).mp rfl
    rw [this, htc']; simp
  -- the set can be written as the union of these two set
  have h6: {x:ℝ | x ∈ Ioo 0 (24 * π) ∧ cos (x/4) = cos x} = s ∪ t := by
    rw [h3, s_def, t_def]
    ext x; simp
    constructor <;> intro h
    · rcases h.right with ⟨m,hm⟩
      rcases hm with hm1 | hm2
      · left; constructor; apply h.left; use m
      · right; constructor; apply h.left; use m
    · rcases h with hh | hh
      <;> refine ⟨hh.left, ?_⟩
      <;> rcases hh.right with ⟨m,hm⟩
      · use m; left; apply hm
      · use m; right; apply hm
  -- notice that 40/5 = 24/3; 80/5 = 48/3, two elements in common.
  have h7: s ∩ t = {8*π, 16*π} := by
    rw [s_def, t_def]
    ext x; simp
    constructor <;> intro h
    · have hl := h.left
      have hr := h.right
      rcases hl.right with ⟨m1,hm1⟩
      rcases hr.right with ⟨m2,hm2⟩
      have hh1: 8/5 * m1 * π = 8/3 * m2 * π := by
        rw [← hm1, ← hm2]
      have hh2: 3*m1 = 5*m2 := by
        have tt1: π ≠ 0 := by linarith [pi_pos]
        have tt2: (↑(3*m1):ℝ) = ↑(5*m2) := by
          simp
          have: (m1:ℝ) = 8/5*m1*π / (8/5*π) := by
            ring_nf; field_simp [tt1]
          rw [this, hh1]; field_simp [tt1]; ring
        apply Int.cast_inj.mp tt2
      have hh3: 5 ∣ 3*m1 := by
        apply Dvd.intro m2 hh2.symm
      have m1lb := (h4 x m1 hl.left.left hl.left.right hm1).left
      have m1ub := (h4 x m1 hl.left.left hl.left.right hm1).right
      have m1eq: m1 = 5 ∨ m1 = 10 := by
        interval_cases m1 <;> norm_num at hh3 <;> simp
      rw [hm1]
      rcases m1eq with mm | mm
      <;> rw [mm] <;> ring_nf <;> tauto
    · rcases h with hh | hh <;> rw [hh]
      <;> constructor <;> simp [pi_pos]
      <;> constructor <;> norm_num
      · use 5; simp
      · use 3; simp
      · use 10; simp; ring_nf; tauto
      · use 6; simp; ring_nf; tauto
  have h8: (s ∩ t).encard = 2 := by
    rw [h7, Set.encard_eq_two]
    use (8*π); use (16*π)
    simp [pi_pos.ne']
  -- by encard + 2 = 14+8, so answer is 14+8-2 = 20
  rw [h6]
  have h9: (s ∪ t).ncard = 20 := by
    have fs: s.Finite := by
      exact finite_of_encard_eq_coe hsc
    have ft: t.Finite := by
      exact finite_of_encard_eq_coe htc
    have nst: (s ∩ t).ncard = 2 := by
      have: (s ∩ t).ncard = (s ∩ t).encard := by
        apply Finite.cast_ncard_eq
        exact Finite.inter_of_right ft s
      rw [← this] at h8
      apply Nat.cast_inj.mp h8
    have := Set.ncard_union_add_ncard_inter s t fs ft
    rw [hsc', htc', nst] at this
    linarith [this]
  have h10: (s ∪ t).encard = (s ∪ t).ncard := by
    have: (s ∪ t).ncard ≠ 0 := by
      rw [h9]; simp
    apply (ENat.toNat_eq_iff this).mp
    rw [Set.ncard]
  rw [h10, h9]; simp