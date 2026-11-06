import Mathlib

open Real Set

/- $\sqrt[4]{10+8 \sin ^{2} x}-\sqrt[4]{8 \cos ^{2} x-1}=1$. -/
theorem algebra_196918 (x : ℝ) (hrad : 0 ≤ 8 * cos x ^ 2 - 1) :
  (10 + 8 * (sin x) ^ 2) ^ (1 / (4 : ℝ)) - (8 * (cos x) ^ 2 - 1) ^ (1 / (4 : ℝ)) = 1 ↔
  ∃ k : ℤ, x = (3 * k - 1) * π / 3 ∨ x = (3 * k + 1) * π / 3 := by
  let u := (10 + 8 * (sin x) ^ 2) ^ (1 / (4 : ℝ))
  let v := (8 * (cos x) ^ 2 - 1) ^ (1 / (4 : ℝ))
  constructor
  · intro h
    --rewrite the equation in terms of u and v
    have eq1 : u - v = 1 := by
      simp only [u, v]
      exact h
    --find u^4 + v^4 = 17 from the fact that sin x ^ 2 + cos x ^ 2 = 1, and get a system of two equations
    have eq2 : u ^ (4 : ℝ) + v ^ (4 : ℝ) = 17 := by
      simp only [u, v]
      rw [← rpow_mul (add_nonneg (by linarith) (mul_nonneg (by linarith) (sq_nonneg (sin x))))]
      rw [← rpow_mul (hrad)]
      ring_nf
      repeat rw [rpow_one]
      ring_nf
      rw [add_assoc, ← add_mul, sin_sq_add_cos_sq]
      linarith
    --with algebraic manipulations on the second equation (u ^ 2 - v ^ 2) ^ 2 + 2 * u ^ 2 * v ^ 2 = 17
    have eq2₁ : (u ^ 2 - v ^ 2) ^ 2 + 2 * u ^ 2 * v ^ 2 = 17 := by
      rw[sub_sq]
      ring_nf
      rw[(by rfl : (4 : ℝ) = (4 : ℕ)), rpow_natCast u 4, rpow_natCast v 4] at eq2
      exact eq2
    --since u-v = 1 then (u ^ 2 - v ^ 2) ^ 2 = ((u - v) * (u + v)) ^ 2 = (u + v) ^ 2
    have eq2₂ : (u - v) ^ 2 + 4 * u * v + 2 * u ^ 2 * v ^ 2 = 17 := by
      rw[sub_sq, (by linarith : u ^ 2 - 2 * u * v + v ^ 2 + 4 * u * v = u ^ 2 + (v ^ 2 + 2 * u * v))]
      rw[add_comm (v ^ 2), ← add_assoc, ← add_sq, ← one_mul (u + v), ← eq1]
      rw[mul_comm, ← sq_sub_sq u v]
      exact eq2₁
    rw[eq1] at eq2₂
    --develop the second equation algebraically
    have eq2₃ : u ^ 2 * v ^ 2 + 2 * u * v - 8 = 0 := by linarith
    have eq2₄ : (u * v + 4) * (u * v - 2) = 0 := by
      ring_nf at eq2₃ ⊢
      exact eq2₃
    rw[mul_eq_zero] at eq2₄
    --the product of two numbers equal 0 if and only if either number is 0
    cases eq2₄ with
    --case u * v + 4 = 0 gives a contradiction because u * v = -4 means that either u or v is negative, but it cannot be by their definitions
    | inl h1 =>
      have : u * v < 0 := by linarith
      have l : u < 0 ∧ v > 0 ∨ u > 0 ∧ v < 0 := by exact (RCLike.ofReal_mul_neg_iff u v).mp this
      obtain l1|l2 := l
      · obtain ⟨l11, l12⟩ := l1
        have : u ≥ 0 := by
          simp[u] at this
          refine rpow_nonneg (add_nonneg (by linarith) (mul_nonneg (by linarith) (sq_nonneg (sin x)))) (1 / 4)
        have contr : 1 < 0 := by linarith
        contradiction
      · obtain ⟨l21, l22⟩ := l2
        have : v ≥ 0 := by
          simp[u] at this
          refine rpow_nonneg hrad (1 / 4)
        have contr : 1 < 0 := by linarith
        contradiction
    --case u * v = 2 is the interesting one and substitute the first equation u = 1 + v
    | inr h2 =>
      --again a product of number is 0 if and only if either is 0.
      have k1 : (v + 2) * (v - 1) = 0 := by
        ring_nf
        rw[(by ring_nf : -2 + v + v ^ 2 = (1 + v) * v - 2)]
        rw[(by constructor; intro h; linarith; intro h; linarith : u - v = 1 ↔ u = 1 + v)] at eq1
        rw[← eq1]
        exact h2
      rw[mul_eq_zero] at k1
      cases k1 with
    -- v = -2 produces contradiction since v cannot be 0 by its definition
    | inl h11 =>
      have : v < 0 := by linarith
      have hnonneg : v ≥ 0 := by
        simp[v] at this
        refine rpow_nonneg hrad (1 / 4)
      have : 1 < 0 := by linarith
      contradiction
    -- v = 1 is the interesting case
    | inr h22 =>
      have hv : v = 1 := by linarith
      --this brings to u = 2 substituting in the first equation
      have hu : u = 2 := by
        rw[hv] at h2
        linarith
      --now we get back our original expressions for u and v and solve
      simp[u, v] at hu hv
      --raise both to the power of 4
      have hu' := congrFun (congrArg HPow.hPow hu) (4 : ℝ)
      have hv' := congrFun (congrArg HPow.hPow hv) (4 : ℝ)
      rw [← rpow_mul (add_nonneg (by linarith) (mul_nonneg (by linarith) (sq_nonneg (sin x))))] at hu'
      rw [← rpow_mul (hrad)] at hv'
      norm_num at hu' hv'
      --we get the system of two equations 4 * sin x ^ 2 = 3 and 4 * cos x ^ 2 = 1
      --which after substituting sin x ^ 2 = 1 - cos x ^ 2 become the same equation
      have eq1fin : 4 * sin x ^ 2 = 3 := by linarith
      have eq2fin : 4 * cos x ^ 2 = 1 := by linarith
      rw[sin_sq] at eq1fin
      ring_nf at eq1fin
      --hence we are left with 4 * cos x ^ 2 = 1 which becomes cos (2 * x) = - (1 / 2)
      --applying the formula of the cosine of the double of an angle
      have : cos (2 * x) = - (1 / 2) := by
        rw[cos_two_mul]
        field_simp
        linarith
      --two cosines are the same if they have the same argument up to adding an integer multiple of 2π
      rw[← cos_pi_div_three, ← Real.cos_pi_sub, cos_eq_cos_iff] at this
      obtain ⟨k,hk1|hk2⟩ := this
      --find the k that makes the angle the same needed for the result in the first case
      · use -k
        right
        push_cast
        field_simp at hk1 ⊢
        ring_nf at hk1
        have : x = (π * 2 - π * k * 6) * 1 / 6 := by linarith
        rw[this]
        ring_nf
        --find the k that makes the angle the same needed for the result in the second case
      · use k
        left
        field_simp at hk2 ⊢
        ring_nf at hk2
        have : x = (π * 2 - π * k * 6) * (- 1 / 6) := by linarith
        rw[this]
        ring_nf
  · intro h
    obtain ⟨k ,hk⟩ := h
    obtain hk1|hk2 := hk
    --take x = (3 * k - 1) * π / 3
    · ring_nf at hk1
      --rewrite the trigonometric equation in a neater way
      rw [sin_sq, hk1, cos_add]
      norm_num
      --substitute x inside the equation
      rw [← mul_div_assoc, mul_one, cos_pi_div_three]
      ring_nf
      by_cases h1 : Even k
      --there are two cases to distinguish: k even and k odd
      --for k even one gets x = - π / 3 suffices to be substituted in which is a known angle
      · unfold Even at h1
        obtain ⟨r, hr⟩ := h1
        rw [← two_mul] at hr
        rw [hr]
        norm_num
        rw [mul_comm 2, mul_assoc, cos_int_mul_two_pi]
        norm_num
        rw [(by norm_num : (16 : ℝ) = 2 ^ (4 : ℝ)), ← rpow_mul (by linarith)]
        rw [← mul_div_assoc, mul_one]
        simp
        --solve the algebraic equation left
        linarith
        --for k odd one gets x = - π / 3 + π suffices to be substituted in
      · rw [← Iff.symm Int.not_even_iff_odd] at h1
        unfold Odd at h1
        obtain ⟨r, hr ⟩ := h1
        rw [hr]
        norm_num
        --split the cosine with the formula for the cosine of a sum
        rw [add_mul, cos_add]
        norm_num
        rw [mul_comm 2, mul_assoc, cos_int_mul_two_pi]
        norm_num
        rw [(by norm_num : (16 : ℝ) = 2 ^ (4 : ℝ)), ← rpow_mul (by linarith)]
        rw [← mul_div_assoc, mul_one]
        simp
        linarith
    --take x = (3 * k + 1) * π / 3
    · ring_nf at hk2
      --rewrite the trigonometric equation in a neater way
      rw [sin_sq, hk2, cos_add]
      norm_num
      --substitute x inside the equation
      rw [← mul_div_assoc, mul_one, cos_pi_div_three]
      ring_nf
      by_cases h1 : Even k
      --there are two cases to distinguish: k even and k odd
      --for k even one gets x = - π / 3 suffices to be substituted in which is a known angle
      · unfold Even at h1
        obtain ⟨r, hr⟩ := h1
        rw [← two_mul] at hr
        rw [hr]
        norm_num
        rw [mul_comm 2, mul_assoc, cos_int_mul_two_pi]
        norm_num
        rw [(by norm_num : (16 : ℝ) = 2 ^ (4 : ℝ)), ← rpow_mul (by linarith)]
        rw [← mul_div_assoc, mul_one]
        simp
        linarith
      · rw [← Iff.symm Int.not_even_iff_odd] at h1
        unfold Odd at h1
        obtain ⟨r, hr ⟩ := h1
        rw [hr]
        norm_num
        rw [add_mul, cos_add]
        norm_num
        rw [mul_comm 2, mul_assoc, cos_int_mul_two_pi]
        norm_num
        rw [(by norm_num : (16 : ℝ) = 2 ^ (4 : ℝ)), ← rpow_mul (by linarith)]
        rw [← mul_div_assoc, mul_one]
        simp
        --solve the algebraic equation left
        linarith