import Mathlib

open Real Set
open scoped BigOperators

/- 1. (5 points) Find the degree measure of the angle


delta=arccos ((sin 2195 + sin 2196 + ... + sin 5795) ^ (cos 2160 + cos 2161 + ... + cos 5760))
-/

theorem algebra_196588 :
  arccos ((∑ i : ℕ in Finset.Icc 2195 5795, sin (i * π / 180)) ^ (∑ i : ℕ in Finset.Icc 2160 5760,
  cos (i * π / 180))) = 55 * π / 180 := by
  -- we know that cos x + cos (pi+x) = 0
  have h0: ∀ x:ℝ, cos x + cos (x+π) = 0 := by intro x; linarith [cos_add_pi x]
  -- same for sin
  have h0': ∀ x:ℝ, sin x + sin (x+π) = 0 := by intro x; linarith [sin_add_pi x]

  -- let's move to Ico's because they are easier to work with
  have hicc:∀ a b:ℕ, Finset.Icc a b = Finset.Ico a (b+1) := by
    intro a b
    ext c; simp; omega
  rw [hicc, hicc]
  -- Let's first show that the exponent is 1
  have h1: (∑ i : ℕ in Finset.Ico 2160 5761, cos (i * π / 180)) = 1 := by
      -- the sum of cosines from 0 to 359 degress covers the unit circle uniformly so it's 0
      have h2: (∑ i : ℕ in Finset.range 360, cos (i * π / 180)) = 0 := by
        -- we can show this by splitting the sum in the middle and then pairing up the terms
        have h3:=Finset.sum_Ico_eq_sum_range (fun i => cos (↑i * π / 180)) 0 360; simp only [Nat.sub_zero, Nat.zero_add] at h3
        rw [← h3, ← Finset.sum_Ico_consecutive (n:=180) (hmn:=by norm_num) (hnk:=by norm_num), Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        simp; rw [← Finset.sum_add_distrib, Finset.sum_eq_zero]
        intro x hx
        calc cos (↑x * π / 180) + cos ((180 + ↑x) * π / 180)
        _ = cos (↑x * π / 180) + cos (↑x * π / 180 + π) := by ring_nf
        _ = 0 := h0 _
      -- a multiple also works
      have h3: ∀ a:ℕ, (∑ i : ℕ in Finset.range (a*360), cos (i * π / 180)) = 0 := by
        intro a
        induction a with
        | zero => simp
        | succ n ih =>
          have h4:=Finset.sum_Ico_eq_sum_range (fun i => cos (↑i * π / 180)) 0 ((n+1)*360); simp only [Nat.sub_zero, Nat.zero_add] at h4
          rw [← h4, ← Finset.sum_Ico_consecutive (n:=n*360) (hmn:=by norm_num) (hnk:=by norm_num), Finset.sum_Ico_eq_sum_range, Nat.sub_zero]; simp [ih, Finset.sum_Ico_eq_sum_range]
          ring_nf; rw [Nat.add_sub_assoc (by norm_num), Nat.sub_self, Nat.add_zero];
          conv =>
            lhs; rhs; intro x;
            calc cos (↑n * π * 2 + ↑x * π * (1 / 180))
            _ = cos ((n:ℤ) * (2 * π) - (-↑x * π * (1 / 180))) := by apply congr_arg cos; simp; ring_nf
            _ = cos (↑x * π / 180) := by rw [cos_int_mul_two_pi_sub, neg_mul, neg_mul, cos_neg]; ring_nf
          exact h2
      rw [Finset.sum_Ico_eq_sum_range]; norm_num
      -- now we can get rid of the 3601
      have h3' := h3 (a:=10); norm_num at h3'
      rw [Finset.sum_range_succ];
      conv =>
        lhs; lhs; rhs; intro x
        calc cos ((2160 + ↑x) * π / 180)
        _ = cos (2160 * π / 180 + ↑x * π / 180) := by ring_nf
        _ = cos ((6:ℤ) * (2 * π) - (-↑x * π / 180)) := by ring_nf
        _ = cos (↑x * π / 180) := by rw [cos_int_mul_two_pi_sub, neg_mul, neg_div, cos_neg];
      rw [h3']; ring_nf;
      calc cos (π * 32)
      _ = cos ((16:ℕ) * (2*π)) := by ring_nf
      _ = 1 := by rw [cos_nat_mul_two_pi]
  rw [h1, rpow_one]
  -- now we go through a similar process for the sine part
  have h2: (∑ i : ℕ in Finset.range 360, sin (i * π / 180)) = 0 := by
    -- we can show this by splitting the sum in the middle and then pairing up the terms
    have h3:=Finset.sum_Ico_eq_sum_range (fun i => sin (↑i * π / 180)) 0 360; simp only [Nat.sub_zero, Nat.zero_add] at h3
    rw [← h3, ← Finset.sum_Ico_consecutive (n:=180) (hmn:=by norm_num) (hnk:=by norm_num), Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    simp; rw [← Finset.sum_add_distrib, Finset.sum_eq_zero]
    intro x hx
    calc sin (↑x * π / 180) + sin ((180 + ↑x) * π / 180)
    _ = sin (↑x * π / 180) + sin (↑x * π / 180 + π) := by ring_nf
    _ = 0 := h0' _
  -- the formula also works for any offset
  have h3: ∀ a:ℕ, (∑ i in Finset.Ico a (a+360), sin (i * π / 180) = 0) := by
    intro a
    rw [Finset.sum_Ico_eq_sum_range, add_comm, Nat.add_sub_assoc (by norm_num), Nat.sub_self, Nat.add_zero]
    -- let's use sin(x+y) = sin x cos y + cos x sin y to simplify
    conv_lhs =>
      rhs; intro k
      calc sin (↑(a + k) * π / 180)
      _ = sin (a * π / 180 + k * π / 180) := by rify; ring_nf
      _ = sin (a * π / 180) * cos (k * π / 180) + cos (a * π / 180) * sin (k * π / 180) := by rw [sin_add]

    -- the sum of cosines from 0 to 359 degress covers the unit circle uniformly so it's 0
    have h2_copy: (∑ i : ℕ in Finset.range 360, cos (i * π / 180)) = 0 := by
      -- we can show this by splitting the sum in the middle and then pairing up the terms
      have h3:=Finset.sum_Ico_eq_sum_range (fun i => cos (↑i * π / 180)) 0 360; simp only [Nat.sub_zero, Nat.zero_add] at h3
      rw [← h3, ← Finset.sum_Ico_consecutive (n:=180) (hmn:=by norm_num) (hnk:=by norm_num), Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      simp; rw [← Finset.sum_add_distrib, Finset.sum_eq_zero]
      intro x hx
      calc cos (↑x * π / 180) + cos ((180 + ↑x) * π / 180)
      _ = cos (↑x * π / 180) + cos (↑x * π / 180 + π) := by ring_nf
      _ = 0 := h0 _
    -- now we can deal with the sum
    calc ∑ k ∈ Finset.range 360, (sin (↑a * π / 180) * cos (↑k * π / 180) + cos (↑a * π / 180) * sin (↑k * π / 180))
    _ = (∑ k ∈ Finset.range 360, (sin (↑a * π / 180) * cos (↑k * π / 180)) + ∑ k ∈ Finset.range 360, cos (↑a * π / 180) * sin (↑k * π / 180)) := by rw [Finset.sum_add_distrib];
    _ = (∑ k ∈ Finset.range 360, (cos (↑k * π / 180) * sin (↑a * π / 180)) + ∑ k ∈ Finset.range 360, sin (↑k * π / 180) * cos (↑a * π / 180)) := by
      conv => lhs; lhs; rhs; intro k; rw [mul_comm];
      conv => lhs; rhs; rhs; intro k; rw [mul_comm];
    _ = (∑ k ∈ Finset.range 360, (cos (↑k * π / 180))) * sin (↑a * π / 180) + (∑ k ∈ Finset.range 360, sin (↑k * π / 180)) * cos (↑a * π / 180) := by rw [Finset.sum_mul, Finset.sum_mul]
    _ = 0 := by rw [h2_copy, h2]; simp;
  -- we can now simplify the expression
  conv_lhs =>
    rhs
    rw [← Finset.sum_Ico_consecutive (n:=2555) (hmn:=by norm_num) (hnk:=by norm_num), h3 2195, zero_add,
        ← Finset.sum_Ico_consecutive (n:=2915) (hmn:=by norm_num) (hnk:=by norm_num), h3 2555, zero_add,
        ← Finset.sum_Ico_consecutive (n:=3275) (hmn:=by norm_num) (hnk:=by norm_num), h3 2915, zero_add,
        ← Finset.sum_Ico_consecutive (n:=3635) (hmn:=by norm_num) (hnk:=by norm_num), h3 3275, zero_add,
        ← Finset.sum_Ico_consecutive (n:=3995) (hmn:=by norm_num) (hnk:=by norm_num), h3 3635, zero_add,
        ← Finset.sum_Ico_consecutive (n:=4355) (hmn:=by norm_num) (hnk:=by norm_num), h3 3995, zero_add,
        ← Finset.sum_Ico_consecutive (n:=4715) (hmn:=by norm_num) (hnk:=by norm_num), h3 4355, zero_add,
        ← Finset.sum_Ico_consecutive (n:=5075) (hmn:=by norm_num) (hnk:=by norm_num), h3 4715, zero_add,
        ← Finset.sum_Ico_consecutive (n:=5435) (hmn:=by norm_num) (hnk:=by norm_num), h3 5075, zero_add,
        ← Finset.sum_Ico_consecutive (n:=5795) (hmn:=by norm_num) (hnk:=by norm_num), h3 5435, zero_add]
    simp;
    calc sin (5795 * π / 180)
    _ = sin ((16:ℕ) * (2 * π) - (-35 * π / 180)) := by norm_num; ring_nf;
    _ = sin (35 * π / 180) := by rw [Real.sin_nat_mul_two_pi_sub, neg_mul, neg_div, Real.sin_neg]; simp
  -- convert from arccos to arcsin
  rw [arccos_eq_pi_div_two_sub_arcsin, arcsin_sin (by ring_nf; rw [mul_comm, mul_comm π]; linarith [pi_nonneg]) (by ring_nf; linarith [pi_nonneg])]; ring_nf