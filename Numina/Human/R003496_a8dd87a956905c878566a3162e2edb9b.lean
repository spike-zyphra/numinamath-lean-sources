import Mathlib

open Real
/- 3. Find the solution to the equation

$$
(\frac{1-\cos (2 x)}{2}\right)^{5}+\left(\frac{1+\cos (2 x)}{2}\right)^{5}=\frac{29}{16} \cos ^{4} (2 x)
$$

-/ 

--the LHS is equivalent to (2 + 20 * (cos (2 * x)) ^ 2 + 10 * (cos (2 * x)) ^ 4) / 32. 
lemma eq1 (x : ℝ) : ((1 - cos (2 * x)) / 2) ^ 5 + ((1 + cos (2 * x)) / 2) ^ 5 = (2 + 20 * (cos (2 * x)) ^ 2 + 10 * (cos (2 * x)) ^ 4) / 32 := by
    rw[div_pow, div_pow, ← add_div]
    norm_num
    field_simp
    --it can be seen by writing the powers in the Newton notation
    rw[add_pow, sub_pow]
    simp
    have : ∑ x_1 ∈ Finset.range 6, (-1) ^ (x_1 + 5) * cos (2 * x) ^ (5 - x_1) * (Nat.choose 5 x_1) +
        ∑ x_1 ∈ Finset.range 6, cos (2 * x) ^ (5 - x_1) * (Nat.choose 5 x_1) =
        ∑ x_1 ∈ Finset.range 6 , (Nat.choose 5 x_1) * (cos (2 * x) ^ (5 - x_1) - (- 1) ^ x_1 * cos (2 * x) ^ (5 - x_1)) := by
      rw[← Finset.sum_add_distrib]
      have eq_sum : ∀ i ∈ Finset.range 6, (-1) ^ (i + 5) * cos (2 * x) ^ (5 - i) * (Nat.choose 5 i) + cos (2 * x) ^ (5 - i) * (Nat.choose 5 i) =
          (Nat.choose 5 i) * (cos (2 * x) ^ (5 - i) - (-1) ^ i * cos (2 * x) ^ (5 - i)) := by
        intro i hi
        ring_nf
      exact (Finset.sum_eq_sum_iff_of_le (by intro i hi; specialize eq_sum i hi; linarith)).2 eq_sum
    rw[this]
    --then noticing that the sum can be split over odd and even numbers less than 6
    have union_fin_6 : Finset.range 6 = Finset.filter (fun n => Even n) (Finset.range 6) ∪ Finset.filter (fun n => Odd n) (Finset.range 6) := by 
      ext x
      simp
      constructor
      all_goals intro h
      · rw[← and_or_left]
        exact ⟨h, by by_cases hx : Even x; left; exact hx; rw[Nat.not_even_iff_odd] at hx; right; exact hx⟩
      · rw[← and_or_left] at h
        exact h.1
    --this is because the two subsets are of course disjoint
    have disjoint_fin_6 : Disjoint (Finset.filter (fun n => Even n) (Finset.range 6)) (Finset.filter (fun n => Odd n) (Finset.range 6)) := by 
      rw[Finset.disjoint_iff_ne]
      intro a ha b hb
      simp at ha hb
      contrapose ha
      push_neg at ha ⊢
      intro a
      rw[Nat.not_even_iff_odd, ha]
      exact hb.2
    rw[union_fin_6, Finset.sum_union disjoint_fin_6]
    have even_eq : Finset.filter (fun n => Even n) (Finset.range 6) = {0, 2, 4} := by  
      ext x
      simp
      constructor
      all_goals intro h
      · simp[Even] at h
        obtain ⟨hle6, r, hr⟩ := h
        rw[← two_mul] at hr
        rw[hr] at hle6 ⊢
        by_cases hr0 : r = 0
        · rw[hr0]
          simp
        · by_cases hr1 : r = 1
          · rw[hr1]
            simp
          · by_cases hr2 : r = 2
            · rw[hr2]
              simp
            · have : r ≥ 3 := by omega
              exfalso
              linarith
      · obtain h0|h2|h4 := h
        · exact ⟨by linarith, by rw[h0]; simp⟩
        · exact ⟨by linarith, by rw[h2]; simp⟩
        · exact ⟨by linarith, by rw[h4, (by linarith : 4 = 2 * 2)]; exact even_two_mul 2⟩
    have odd_eq : Finset.filter (fun n => Odd n) (Finset.range 6) = {1, 3, 5} := by 
      ext x
      simp
      constructor
      all_goals intro h
      · simp[Odd] at h
        obtain ⟨hle6, r, hr⟩ := h
        rw[hr] at hle6 ⊢
        by_cases hr0 : r = 0
        · rw[hr0]
          simp
        · by_cases hr1 : r = 1
          · rw[hr1]
            simp
          · by_cases hr2 : r = 2
            · rw[hr2]
              simp
            · have : r ≥ 3 := by omega
              exfalso
              linarith
      · obtain h1|h3|h5 := h
        · exact ⟨by linarith, by rw[h1]; simp⟩
        · exact ⟨by linarith, by rw[h3]; simp[Odd]⟩
        · exact ⟨by linarith, by rw[h5]; simp[Odd]; use 2; norm_num⟩
    --and algebraic calculations yield the claim
    rw[even_eq, odd_eq]
    simp
    ring_nf
    norm_num
    rw[mul_assoc]
    norm_cast

--we have the useful fact that cos (π * (1 / 4) + π * k * (1 / 2)) can either attain the value √2/2 or -√2/2 
lemma cos_eq_cases (k : ℤ) : cos (π * (1 / 4) + π * k * (1 / 2)) = cos (π / 4) ∨
    cos (π * (1 / 4) + π * k * (1 / 2)) = - cos (π / 4) := by 
  rw[cos_add]
  rw[(by ring_nf : π * (1 / 4) = π / 4), cos_pi_div_four, sin_pi_div_four]
  rw[← mul_sub]
  rw[(by ring_nf : -(√2 / 2) = √2 / 2 * (-1))]
  nth_rw 2 [← mul_one (√2/2)]
  --it can be seen by arguing on k mod 4 and using the usual properties of the sin/cos of addition and 
  --standard forms of translations of sin and cosine for known angles.
  mod_cases H : k % 4
  all_goals 
    rw[Int.modEq_comm, Int.modEq_iff_dvd, dvd_iff_exists_eq_mul_right] at H
    obtain ⟨c, hc⟩ := H
  · left
    simp at hc
    rw[hc]
    push_cast
    ring_nf
    rw[(by ring_nf : π * c * 2 = c * (2 * π)), cos_int_mul_two_pi c, Real.sin_eq_zero_iff.2 (by use (2 * c); push_cast; ring_nf)]
    ring_nf
  · right
    have : k = 4 * c + 1 := by linarith
    rw[this]
    push_cast
    ring_nf
    rw[(by ring_nf : π * c * 2 = c * (2 * π)), cos_add_int_mul_two_pi (π * (1/2)) c, sin_add_int_mul_two_pi (π * (1/2)) c]
    rw[(by ring_nf : π * (1/2) = π / 2), cos_pi_div_two, sin_pi_div_two]
    ring_nf
  · right
    have : k = 4 * c + 2 := by linarith
    rw[this]
    push_cast
    ring_nf
    rw[(by ring_nf : π * c * 2 = c * (2 * π)), cos_add_int_mul_two_pi π c, sin_add_int_mul_two_pi π c]
    rw[cos_pi, sin_pi]
    ring_nf
  · left
    have : k = 4 * c + 3 := by linarith
    rw[this]
    push_cast
    ring_nf
    rw[(by ring_nf : π * c * 2 = c * (2 * π)), cos_add_int_mul_two_pi (π * (3/2)) c, sin_add_int_mul_two_pi (π * (3/2)) c]
    rw[(by ring_nf : π * (3/2) = π / 2 + π), cos_add_pi, sin_add_pi]
    rw[cos_pi_div_two, sin_pi_div_two]
    ring_nf

theorem algebra_188682 (x : ℝ) :
    ((1 - cos (2 * x)) / 2) ^ 5 + ((1 + cos (2 * x)) / 2) ^ 5 =
    (29 / 16) * (cos (2 * x)) ^ 4 ↔
    (∃ k : ℤ, x = π / 8 + k * π / 4) := by
  constructor
  all_goals intro h
  --rw the LHS given in the first lemma
  · rw[eq1] at h
    have eq2 : 2* (24 * (cos (2 * x)) ^ 4 - 10 * (cos (2 * x)) ^ 2 - 1) = 0 := by field_simp at h; ring_nf at h ⊢; linarith
    rw[mul_eq_zero] at eq2
    simp at eq2

    have eq_roots : 24 * (((cos (2 * x)) ^ 2 - 1 / 2) * ((cos (2 * x)) ^ 2 + 1 / 12)) = 0 := by
      rw[mul_add, sub_mul, sub_mul];
      field_simp
      linarith
    rw[mul_eq_zero] at eq_roots
    simp at eq_roots
    --after algebraic manipulations and the formula for the cosine of twice an angle, one gets that either cos(2 * x) ^ 2 = 1/2 or cos(2 * x) ^ 2 = -1/12 (which can be excluded by contradiction)
    obtain root1|root2 := eq_roots
    --the case when cos(2 * x) ^ 2 = 1/2 is possible when π / 2 = 2 * ↑k * π + 2 * (2 * x) ∨ π / 2 = 2 * ↑k * π - 2 * (2 * x) and solving via algebra yields the result.
    · have cos_four_mul : cos (2 * (2 * x)) = 0 := by
        rw[cos_two_mul]
        rw[← one_div] at root1
        field_simp at root1
        linarith
      rw[← cos_pi_div_two] at cos_four_mul
      rw[cos_eq_cos_iff] at cos_four_mul
      obtain ⟨k', hk'1|hk'2⟩ := cos_four_mul
      · use (-2 * k')
        push_cast
        field_simp at hk'1 ⊢
        ring_nf at hk'1 ⊢
        linarith
      · use (-1 + 2 * k')
        push_cast
        field_simp at hk'2 ⊢
        ring_nf at hk'2 ⊢
        linarith
    --the case cos^2(2x) = -1/12 cannot happen since cos^2 cannot be negative.
    · have : cos (2 * x) ^ 2 = - 1 / 12 := by rw[← one_div] at root2; linarith
      have : cos (2 * x) ^ 2 ≥ 0 := by exact sq_nonneg (cos (2 * x))
      exfalso
      linarith
  --we substitute the two angles and by algebra and properties of sine and cosine discussed above, the claim holds
  · obtain ⟨k, hk⟩ := h
    rw[eq1, hk]
    ring_nf
    obtain cos1|cos2 := cos_eq_cases k
    · rw[cos1, cos_pi_div_four]
      ring_nf
      rw[(by ring_nf : √2 ^ 4 = (√2 ^ 2) ^ 2), sq_sqrt (by linarith)]
      ring_nf
    · rw[cos2, cos_pi_div_four]
      ring_nf
      rw[(by ring_nf : √2 ^ 4 = (√2 ^ 2) ^ 2), sq_sqrt (by linarith)]
      ring_nf