import Mathlib

/- Which positive integers can be written in the form \[\frac{\operatorname{lcm}(x, y) + \operatorname{lcm}(y, z)}{\operatorname{lcm}(x, z)}\] for positive integers  $x$ ,  $y$ ,  $z$ ?-/
theorem number_theory_8532 {n : ℕ} (hnpos : 0 < n) :
    (∃ x y z : ℕ+, (n : ℚ) = (x.lcm y + y.lcm z) / x.lcm z) ↔ Even n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  swap
  -- It is pretty easy to see that any positive even integer works as we have the construction  $(a, a^2, a)$ .
  . rintro ⟨a, ha⟩
    have hapos : 0 < a := by omega
    have hasqpos : 0 < a ^ 2 := by nlinarith
    have lcm_a_asq : a.lcm (a ^ 2) = a ^ 2 := by
      nth_rw 1 [← mul_one a]
      rw [pow_two, Nat.lcm_mul_left, Nat.lcm_one_left]
    have lcm_asq_a : (a ^ 2).lcm a = a ^ 2 := by rwa [Nat.lcm_comm]
    use ⟨a, hapos⟩, ⟨a ^ 2, hasqpos⟩, ⟨a, hapos⟩
    simp [lcm_a_asq, lcm_asq_a, ha]
    field_simp
    ring
  -- Need positive condition to use theorem related to padicValNat
  rintro ⟨x, y, z, hxyz⟩
  have lcm_xy_pos : 0 < x.val.lcm y.val := (x.lcm y).property
  have lcm_yz_pos : 0 < y.val.lcm z.val := (y.lcm z).property
  have lcm_xz_pos : 0 < x.val.lcm z.val := (x.lcm z).property
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases z with ⟨z, hz⟩
  change 0 < x.lcm y at lcm_xy_pos
  change 0 < y.lcm z at lcm_yz_pos
  change 0 < x.lcm z at lcm_xz_pos
  field_simp at hxyz
  -- Now we need to prove that there are no odd integers that can be expressed this way. Assume  $ \frac { \operatorname{lcm} (x,y) +\operatorname {lcm} (y,z) }{\operatorname {lcm} (z, x)}$  can be odd.
  by_contra not_even
  -- $v_2 \left ( \frac { \operatorname{lcm} (x,y) +\operatorname {lcm} (y,z) }{\operatorname {lcm} (z, x)} \right) =0$ ,
  -- $v_2(\operatorname{lcm} (x,y) +\operatorname {lcm} (y,z)) = v_2(\operatorname{lcm}(x, z))$ .
  have v2n_eq_zero : padicValNat 2 n = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rwa [even_iff_two_dvd] at not_even
  norm_cast at hxyz
  apply_fun (padicValNat 2 ·) at hxyz
  rw [padicValNat.mul (by positivity) (by omega), v2n_eq_zero, zero_add] at hxyz
  -- vp(lcm(a,b)) = max (vp(a), vp(b))
  have vp_lcm {p a b : ℕ} (hpp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
      padicValNat p (a.lcm b) = max (padicValNat p a) (padicValNat p b) := by
    have := Nat.factorization_lcm ha.ne' hb.ne'
    repeat rw [← Nat.factorization_def _ hpp]
    apply_fun (· p) at this
    convert this using 1
  have v2_lcm_xz := vp_lcm Nat.prime_two hx hz
  have v2_lcm_xy := vp_lcm Nat.prime_two hx hy
  have v2_lcm_yz := vp_lcm Nat.prime_two hy hz
  -- Let  $v_2(x) = a, v_2(y)=b, v_2(z)=c$ ,
  set a := padicValNat 2 x
  set b := padicValNat 2 y
  set c := padicValNat 2 z
  have eq_of_ne (h : max a b ≠ max b c) : max a c = min (max a b) (max b c) := by
    rw [← v2_lcm_xz, hxyz]
    rify
    -- If v2(lcm(x,y)) ≠ v2(lcm(y,z)) then v2(lcm(x,y)+lcm(y,z)) = min(v2(lcm(x,y)), v2(lcm(y,z)))
    rw [padicValRat.add_eq_min]
    norm_cast
    rw [v2_lcm_xy, v2_lcm_yz]
    any_goals norm_cast; positivity
    norm_cast
    rwa [v2_lcm_xy, v2_lcm_yz]
  have gt_of_eq (h : max a b = max b c) : max a c > min (max a b) (max b c) := by
    suffices max a b + 1 ≤ max a c by
      rw [← h, min_self]
      linarith
    have := Nat.not_dvd_ord_compl Nat.prime_two lcm_xy_pos.ne'
    have := Nat.not_dvd_ord_compl Nat.prime_two lcm_yz_pos.ne'
    have := Nat.not_dvd_ord_compl Nat.prime_two lcm_xz_pos.ne'
    have two_pow_dvd_lcm_xy := Nat.ord_proj_dvd (x.lcm y) 2
    have two_pow_dvd_lcm_yz := Nat.ord_proj_dvd (y.lcm z) 2
    rcases two_pow_dvd_lcm_xy with ⟨s, hs⟩
    rcases two_pow_dvd_lcm_yz with ⟨t, ht⟩
    have sodd := Nat.not_dvd_ord_compl Nat.prime_two lcm_xy_pos.ne'
    have todd := Nat.not_dvd_ord_compl Nat.prime_two lcm_yz_pos.ne'
    nth_rw 1 [hs] at sodd
    nth_rw 1 [ht] at todd
    rw [mul_comm, Nat.mul_div_cancel _ (by positivity),
      ← even_iff_two_dvd, Nat.not_even_iff_odd] at sodd todd
    -- If v2(lcm(x,y)) = v2(lcm(y,z)) then v2(lcm(x,y)+lcm(y,z)) > min(v2(lcm(x,y)), v2(lcm(y,z)))
    have : 2 ^ (max a b + 1) ∣ x.lcm y + y.lcm z := by
      rcases sodd with ⟨p, hp⟩
      rcases todd with ⟨q, hq⟩
      rw [hs, ht, hp, hq]
      use p + q + 1
      repeat rw [Nat.factorization_def _ Nat.prime_two]
      rw [v2_lcm_xy, v2_lcm_yz, ← h]
      ring
    rwa [padicValNat_dvd_iff_le (by positivity), ← hxyz, v2_lcm_xz] at this
  --  and WLOG  $a \leq b \leq c$ .
  rcases le_or_lt a b with hable | hbalt
  . rcases le_or_lt c a with hcale | haclt
    -- c ≤ a ≤ b
    . have h1 : max a b = b := max_eq_right (by linarith)
      have h2 : max b c = b := max_eq_left (by linarith)
      have h3 : max a c = a := max_eq_left (by linarith)
      have h4 : min b b = b := min_eq_left (by linarith)
      rw [h1, h2, h3, h4] at eq_of_ne gt_of_eq
      have : a > b := gt_of_eq (Eq.refl _)
      linarith
    rcases le_or_lt c b with hcble | hbclt
    -- a < c ≤ b
    . have h1 : max a b = b := max_eq_right (by linarith)
      have h2 : max b c = b := max_eq_left (by linarith)
      have h3 : max a c = c := max_eq_right (by linarith)
      have h4 : min b b = b := min_eq_left (by linarith)
      rw [h1, h2, h3, h4] at eq_of_ne gt_of_eq
      have : c > b := gt_of_eq (Eq.refl _)
      linarith
    -- a ≤ b < c
    have h1 : max a b = b := max_eq_right (by linarith)
    have h2 : max b c = c := max_eq_right (by linarith)
    have h3 : max a c = c := max_eq_right (by linarith)
    have h4 : min b c = b := min_eq_left (by linarith)
    rw [h1, h2, h3, h4] at eq_of_ne gt_of_eq
    exact (eq_or_ne b c).elim
      (fun h => (gt_of_eq h).ne h)
      (fun h => h (eq_of_ne h).symm)
  rcases le_or_lt c b with hcble | hbclt
  -- c ≤ b < a
  . have h1 : max a b = a := max_eq_left (by linarith)
    have h2 : max b c = b := max_eq_left (by linarith)
    have h3 : max a c = a := max_eq_left (by linarith)
    have h4 : min a b = b := min_eq_right (by linarith)
    rw [h1, h2, h3, h4] at eq_of_ne gt_of_eq
    exact (eq_or_ne a b).elim
      (fun h => (gt_of_eq h).ne' h)
      (fun h => h (eq_of_ne h))
  -- b < c ≤ a
  rcases le_or_lt c a with hcale | haclt
  . have h1 : max a b = a := max_eq_left (by linarith)
    have h2 : max b c = c := max_eq_right (by linarith)
    have h3 : max a c = a := max_eq_left (by linarith)
    have h4 : min a c = c := min_eq_right (by linarith)
    rw [h1, h2, h3, h4] at eq_of_ne gt_of_eq
    exact (eq_or_ne a c).elim
      (fun h => (gt_of_eq h).ne' h)
      (fun h => h (eq_of_ne h))
  -- b < a < c
  have h1 : max a b = a := max_eq_left (by linarith)
  have h2 : max b c = c := max_eq_right (by linarith)
  have h3 : max a c = c := max_eq_right (by linarith)
  have h4 : min a c = a := min_eq_left (by linarith)
  rw [h1, h2, h3, h4] at eq_of_ne gt_of_eq
  exact (eq_or_ne a c).elim
    (fun h => (gt_of_eq h).ne h)
    (fun h => h (eq_of_ne h).symm)
