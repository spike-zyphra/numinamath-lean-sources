import Mathlib

open Real Set
open scoped BigOperators

/- Let $a, b$, and $c$ be positive real numbers satisfying $\min (a+b, b+c, c+a)>\sqrt{2}$ and $a^{2}+b^{2}+c^{2}=3$. Prove that  $$ \frac{a}{(b+c-a)^{2}}+\frac{b}{(c+a-b)^{2}}+\frac{c}{(a+b-c)^{2}} \geq \frac{3}{(a b c)^{2}} $$  Throughout both solutions, we denote the sums of the form $f(a, b, c)+f(b, c, a)+f(c, a, b)$ by $\sum f(a, b, c)$. -/

set_option maxHeartbeats 500000

lemma titu_generalized {ι : Type*} [Fintype ι] [Nonempty ι] {p : ℝ} (hp : 0 < p) {x a : ι → ℝ}
  (hx : ∀ i, 0 < x i) (ha : ∀ i, 0 < a i) :
  ∑ i, x i ^ (p+1) / a i ^ p ≥ (∑ i, x i) ^ (p+1) / (∑ i, a i) ^ p := by
  -- set exponents for Hölder: r = (p+1)/p, s = p+1
  let r := (p+1) / p
  let s := p+1
  have hr : 1 < r := by
    dsimp [r]
    rw [one_lt_div hp]
    linarith
  have hs : 1 < s := by
    dsimp [s]
    linarith
  have hrecip : r⁻¹ + s⁻¹ = 1 := by
    dsimp [r, s]
    field_simp [hp.ne']

  -- have holder_congr : HolderConjugate r s := ⟨(by norm_num [hrecip]), by positivity, by positivity⟩

  have holder_congr : r.IsConjExponent s := by exact { one_lt := hr, inv_add_inv_conj := hrecip }

  -- define f_i and g_i so that f_i^r = a_i and g_i^s = x_i^(p+1)/a_i^p
  let f : ι → ℝ := fun i => a i ^ (p/(p+1))
  let g : ι → ℝ := fun i => x i / a i ^ (p/(p+1))

  have h_pos_f : ∀ i, 0 < f i := by intro i; exact rpow_pos_of_pos (ha i) _
  have h_pos_g : ∀ i, 0 < g i := by intro i; exact div_pos (hx i) (rpow_pos_of_pos (ha i) _)

  -- ∑ f_i * g_i = ∑ x_i
  have sum_fg : ∑ i, f i * g i = ∑ i, x i := by
    simp only [f, g]
    congr 1
    ext i
    field_simp [ne_of_gt (rpow_pos_of_pos (ha i) _)]

  have sum_fg_pos : 0 < ∑ i, f i * g i := by
    rw [sum_fg]
    apply Finset.sum_pos
    · intro i _
      exact hx i
    · exact Finset.univ_nonempty

  have sum_fi : ∑ i, |f i| ^ r = ∑ i, a i := by
    simp only [f]
    congr 1
    ext i
    rw [abs_of_pos (h_pos_f i)]
    -- Now prove f i ^ r = a i
    simp only [f, r]
    rw [← Real.rpow_mul (by linarith [ha i]: 0 ≤ a i) (p / (p + 1)) ((p + 1) / p)]
    field_simp

  have sum_gi : ∑ i, |g i| ^ s = ∑ i, x i ^ (p+1) / a i ^ p := by
    simp only [g]
    congr 1
    ext i
    rw [abs_of_pos (h_pos_g i)]
    -- Now prove g i ^ s = x i ^ (p+1) / a i ^ p
    simp only [g, s]

    have h_ai_pow : 0 ≤ a i ^ (p / (p + 1)) := by exact Real.rpow_nonneg (le_of_lt (ha i)) _

    rw [div_rpow (by linarith [hx i]: 0 ≤ x i) h_ai_pow (p + 1)]
    rw [← Real.rpow_mul (by linarith [ha i]: 0 ≤ a i) (p / (p + 1)) _]
    field_simp


  -- apply Hölder's inequality
  have H : ∑ i, f i * g i ≤ (∑ i, |f i| ^ r) ^ (1 / r) * (∑ i, |g i| ^ s) ^ (1 / s) := Real.inner_le_Lp_mul_Lq (Finset.univ : Finset ι) f g holder_congr

  have : (∑ i, x i) ^ (p+1) ≤ (∑ i, a i) ^ p * (∑ i, x i ^ (p+1) / a i ^ p) := by
    calc
      (∑ i, x i) ^ (p+1)
        = (∑ i, f i * g i) ^ (p+1) := by rw [sum_fg]
      _ ≤ ((∑ i, |f i| ^ r) ^ (1 / r) * (∑ i, |g i| ^ s) ^ (1 / s)) ^ (p+1) := by
        apply rpow_le_rpow
        · exact le_of_lt sum_fg_pos
        · exact H
        · linarith
      _ = ((∑ i, a i) ^ (1 / ((p+1) / p)) * (∑ i, x i ^ (p+1) / a i ^ p) ^ (1 / (p+1))) ^ (p+1) := by rw [sum_fi, sum_gi]
      _ = ((∑ i, a i) ^ (p / (p+1)) * (∑ i, x i ^ (p+1) / a i ^ p) ^ (1 / (p+1))) ^ (p+1) := by field_simp [hp.ne']
      _ = ((∑ i, a i) ^ (p / (p+1))) ^ (p+1) * ((∑ i, x i ^ (p+1) / a i ^ p) ^ (1 / (p+1))) ^ (p+1) := by
        rw [mul_rpow]
        · exact rpow_nonneg (Finset.sum_nonneg (fun i _ => le_of_lt (ha i))) _
        · exact rpow_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (rpow_nonneg (le_of_lt (hx i)) _) (rpow_nonneg (le_of_lt (ha i)) _))) _

      _ = (∑ i, a i) ^ p * (∑ i, x i ^ (p+1) / a i ^ p) := by
        have h1 : ((∑ i, a i) ^ (p / (p+1))) ^ (p+1) = (∑ i, a i) ^ p := by
          rw [← rpow_mul (Finset.sum_nonneg (fun i _ => le_of_lt (ha i))) (p / (p+1)) (p+1)]
          congr 2
          field_simp [hp.ne']
        have h2 : ((∑ i, x i ^ (p+1) / a i ^ p) ^ (1 / (p+1))) ^ (p+1) = (∑ i, x i ^ (p+1) / a i ^ p) := by
          rw [← rpow_mul (Finset.sum_nonneg (fun i _ => div_nonneg (rpow_nonneg (le_of_lt (hx i)) _) (rpow_nonneg (le_of_lt (ha i)) _))) (1 / (p+1)) (p+1)]
          rw [one_div_mul_cancel (ne_of_gt (by linarith : (0 : ℝ) < p+1)), rpow_one]
        rw [h1, h2]

    -- divide both sides by sum a_i > 0
  rw [ge_iff_le]
  have h_pos :(∑ i, a i) ^ p > 0 := by
    apply rpow_pos_of_pos
    apply Finset.sum_pos
    · intro i _
      exact ha i
    · exact Finset.univ_nonempty
  exact (div_le_iff₀' h_pos).mpr this



lemma pow_eq_rpow_5_2 {a : ℝ} (ha : 0 ≤ a): (a^(5 / 2: ℝ))^2 = a^5 := by
  rw [← Real.rpow_natCast (a^(5 / 2: ℝ)) 2]
  have: (a^(5 / 2: ℝ))^(2: ℝ) = a^(5: ℝ) := by
    rw [← Real.rpow_mul (by positivity) (5 / 2: ℝ) (2: ℝ)]
    norm_num
  simp [this]
  norm_cast

lemma titu_p_2 {a b c: ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (Ia : 0 < b + c - a) (Ib : 0 < c + a - b) (Ic : 0 < a + b - c) :
   ((a^2)^3 / (a^5 * (b + c - a)^2) + (b^2)^3 / (b^5 * (c + a - b)^2) + (c^2)^3 / (c^5 * (a + b - c)^2))
    ≥ (a^2 + b^2 + c^2)^3 / (a^(5 / 2 : ℝ) * (b + c - a) + b^(5 / 2 : ℝ) * (c + a - b) + c^(5 / 2 : ℝ) * (a + b - c))^2  := by
  -- Let p = 2
  have hp : 0 < 2 := by norm_num
  let X : Fin 3 → ℝ
    | 0 => a^2
    | 1 => b^2
    | 2 => c^2
  let A : Fin 3 → ℝ
    | 0 => a^(5/2 : ℝ)*(b + c - a)
    | 1 => b^(5/2 : ℝ)*(c + a - b)
    | 2 => c^(5/2 : ℝ)*(a + b - c)

  have hX : ∀ i, 0 < X i := by
    intro i; fin_cases i <;> dsimp [X] <;> positivity
  have hA : ∀ i, 0 < A i := by
    intro i; fin_cases i <;> dsimp [A]
    · exact mul_pos (Real.rpow_pos_of_pos ha _) Ia
    · exact mul_pos (Real.rpow_pos_of_pos hb _) Ib
    · exact mul_pos (Real.rpow_pos_of_pos hc _) Ic
  -- Apply the generalized Titu's lemma
  have hsum := titu_generalized (p := 2) (by norm_num) hX hA

  calc (a^2)^3 / (a^5 * (b + c - a)^2) + (b^2)^3 / (b^5 * (c + a - b)^2) + (c^2)^3 / (c^5 * (a + b - c)^2)
      = (a^2)^3 / (a^(5 / 2 : ℝ) * (b + c - a))^2 + (b^2)^3 / (b^(5 / 2 : ℝ) * (c + a - b))^2 + (c^2)^3 / (c^(5 / 2 : ℝ) * (a + b - c))^2 := by
        repeat rw [mul_pow]
        repeat rw [← pow_eq_rpow_5_2 (by positivity)]
    _ = ∑ i, X i ^ (2 + 1: ℝ) / A i ^ (2: ℝ) := by
      norm_cast
      simp only [X, A, Fin.sum_univ_three]
    _ ≥ (∑ i, X i) ^ (2 + 1: ℝ) / (∑ i, A i) ^ (2: ℝ) := hsum
    _ = (a^2 + b^2 + c^2)^3 / (a^(5 / 2 : ℝ) * (b + c - a) + b^(5 / 2 : ℝ) * (c + a - b) + c^(5 / 2 : ℝ) * (a + b - c))^2 := by
      simp only [X, A, Fin.sum_univ_three]
      norm_num
      norm_cast


/-- A short proof of Schur's inequality for nonnegative x ≥ y ≥ z and t > 0. -/
lemma schur_inequality_ordered {x y z t : ℝ} (hxy : x ≥ y) (hyz : y ≥ z) (hz : 0 ≤ z) (ht : t > 0) :
    x ^ t * (x - y) * (x - z) +
    y ^ t * (y - z) * (y - x) +
    z ^ t * (z - x) * (z - y) ≥ 0 := by
  -- Rearrange into a sum of nonnegative terms
  have hy : 0 ≤ y := by linarith
  have hx : 0 ≤ x := by linarith
  have h₁ : (x - y) * (x ^ t * (x - z) - y ^ t * (y - z)) + z ^ t * (x - z) * (y - z) ≥ 0 := by
    -- First term: (x - y) ≥ 0
    have hxy' : 0 ≤ x - y := by rwa [sub_nonneg]
    -- Second factor: x^t * (x - z) - y^t * (y - z) ≥ 0
    have hsub : x - z ≥ 0 := by linarith [hxy, hyz, hx]
    have hyz' : 0 ≤ y - z := by rwa [sub_nonneg]
    -- Expand the difference
    have hexpand : x ^ t * (x - z) - y ^ t * (y - z) = (x ^ t - y ^ t) * (x - z) + y ^ t * (x - y) := by ring
    -- Powers are monotone when base ≥ 0
    have hpow : 0 ≤ x ^ t - y ^ t := by
      apply sub_nonneg.mpr
      apply Real.rpow_le_rpow hy hxy (le_of_lt ht)
    -- Each part is nonnegative
    have hpart1 : 0 ≤ (x ^ t - y ^ t) * (x - z) := mul_nonneg hpow hsub
    have hpart2 : 0 ≤ y ^ t * (x - y) := mul_nonneg (Real.rpow_nonneg hy t) hxy'
    -- Combine
    have hdiff : 0 ≤ (x ^ t * (x - z) - y ^ t * (y - z)) := by rw [hexpand]; exact add_nonneg hpart1 hpart2
    -- Third term z^t * (x - z) * (y - z) ≥ 0
    have hzpow_nonneg : 0 ≤ z ^ t := Real.rpow_nonneg hz t
    have hterm3 : 0 ≤ z ^ t * (x - z) * (y - z) := by
      apply mul_nonneg
      apply mul_nonneg hzpow_nonneg hsub
      exact hyz'
    -- Sum of nonnegatives
    exact add_nonneg (mul_nonneg hxy' hdiff) hterm3
  -- Finish by observing rearrangement equals the original sum
  have hrewrite :
    (x - y) * (x ^ t * (x - z) - y ^ t * (y - z)) + z ^ t * (x - z) * (y - z)
      = x ^ t * (x - y) * (x - z) + y ^ t * (y - z) * (y - x) + z ^ t * (z - x) * (z - y) := by ring
  rwa [hrewrite] at h₁


lemma schur_inequality {x y z t : ℝ}
  (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) :
  x^t * (x - y) * (x - z)
    + y^t * (y - z) * (y - x)
    + z^t * (z - x) * (z - y) ≥ 0 := by
  -- Use symmetry to reduce to the ordered case
  wlog hxy : x ≥ y
  · -- When x < y, swap x and y
    have : y^t * (y - x) * (y - z) + x^t * (x - z) * (x - y) + z^t * (z - y) * (z - x) ≥ 0 := by
      apply this hy hx hz ht
      linarith
    convert this using 1
    ring
  -- Now we have x ≥ y, next handle y vs z ordering
  by_cases hyz : y ≥ z
  · -- Case: x ≥ y ≥ z (ordered case)
    exact schur_inequality_ordered hxy hyz hz ht
  · -- Case: x ≥ y but y < z, so we have z > y
    push_neg at hyz
    have hzy : z > y := hyz
    -- We need to consider two subcases: x ≥ z or z > x
    by_cases hxz : x ≥ z
    · -- Subcase: x ≥ z ≥ y, apply ordered inequality
      have : x^t * (x - z) * (x - y) + z^t * (z - y) * (z - x) + y^t * (y - x) * (y - z) ≥ 0 := by
        apply schur_inequality_ordered hxz (le_of_lt hzy) hy ht
      convert this using 1
      ring
    · -- Subcase: z > x ≥ y, apply with z as largest
      push_neg at hxz
      have : z^t * (z - x) * (z - y) + x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) ≥ 0 := by
        apply schur_inequality_ordered (le_of_lt hxz) hxy hy ht
      convert this using 1
      ring


lemma schur_inequality_equiv_form (a b c : ℝ) (ha : 0 < a) : a^((3:ℝ)/2) * (a - b) * (a - c) = a^((7:ℝ)/2) - a^((5:ℝ)/2)*(b + c) + a^((3:ℝ)/2)*b*c := by
    have ha_pos : 0 < a := ha
    have h32_add_2 : (3:ℝ)/2 + 2 = (7:ℝ)/2 := by norm_num
    have h32_add_1 : (3:ℝ)/2 + 1 = (5:ℝ)/2 := by norm_num
    calc
      _ = a^((3:ℝ)/2) * (a^2 - a*c - a*b + b*c) := by ring
      _ = a^((3:ℝ)/2) * a^2 - a^((3:ℝ)/2) * a * c - a^((3:ℝ)/2) * a * b + a^((3:ℝ)/2) * b * c := by ring
      _ = a^((3:ℝ)/2) * a^(2:ℝ) - a^((3:ℝ)/2) * a^(1:ℝ) * c - a^((3:ℝ)/2) * a^(1:ℝ) * b + a^((3:ℝ)/2) * b * c := by simp [Real.rpow_two, Real.rpow_one]
      _ = a^((7:ℝ)/2) - a^((5:ℝ)/2) * c - a^((5:ℝ)/2) * b + a^((3:ℝ)/2) * b * c := by
        simp only [← Real.rpow_add ha_pos]
        norm_num
      _ = a^((7:ℝ)/2) - a^((5:ℝ)/2)*(b + c) + a^((3:ℝ)/2)*b*c := by ring

lemma sum_pow_inequality {a b c : ℝ}
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a^(5/2 : ℝ)*(b + c - a)
    + b^(5/2 : ℝ)*(c + a - b)
    + c^(5/2 : ℝ)*(a + b - c)
  ≤ a * b * c * (a^(1/2 : ℝ) + b^(1/2 : ℝ) + c^(1/2 : ℝ)) := by
  -- Apply Schur inequality with t = 3/2
  have h_schur := schur_inequality (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
    (by norm_num : 0 < (3 / 2 : ℝ))
  -- Expand each term: (a-b)*(a-c) = a^2 - a*(b+c) + b*c, then factor
  have h_expanded :
    (a^(7/2:ℝ) - a^(5/2:ℝ)*(b + c) + a^(3/2:ℝ)*b*c)
      + (b^(7/2:ℝ) - b^(5/2:ℝ)*(c + a) + b^(3/2:ℝ)*c*a)
      + (c^(7/2:ℝ) - c^(5/2:ℝ)*(a + b) + c^(3/2:ℝ)*a*b) ≥ 0 := by
    -- This follows from Schur inequality by expanding (x-y)*(x-z)
    have h1 : a^((3:ℝ)/2) * (a - b) * (a - c) = a^((7:ℝ)/2) - a^((5:ℝ)/2)*(b + c) + a^((3:ℝ)/2)*b*c := schur_inequality_equiv_form a b c ha

    have h2 : b^((3:ℝ)/2) * (b - c) * (b - a) = b^((7:ℝ)/2) - b^((5:ℝ)/2)*(c + a) + b^((3:ℝ)/2)*c*a := schur_inequality_equiv_form b c a hb

    have h3 : c^((3:ℝ)/2) * (c - a) * (c - b) = c^((7:ℝ)/2) - c^((5:ℝ)/2)*(a + b) + c^((3:ℝ)/2)*a*b := schur_inequality_equiv_form c a b hc

    rw [←h1, ←h2, ←h3]
    exact h_schur

  have :
    (a^(7/2:ℝ) - a^(5/2:ℝ)*(b + c))
      + (b^(7/2:ℝ) - b^(5/2:ℝ)*(c + a))
      + (c^(7/2:ℝ) - c^(5/2:ℝ)*(a + b)) + a^(3/2:ℝ)*b*c + b^(3/2:ℝ)*c*a + c^(3/2:ℝ)*a*b ≥ 0 := by linarith

  have h_final : a^(5/2 : ℝ)*(b + c - a)
    + b^(5/2 : ℝ)*(c + a - b)
    + c^(5/2 : ℝ)*(a + b - c)
    - a * b * c * (a^(1/2 : ℝ) + b^(1/2 : ℝ) + c^(1/2 : ℝ)) ≤ 0:= by calc
    _ = a^(5/2 : ℝ) * (b + c) - a^(5/2 : ℝ) * a + b^(5/2 : ℝ) * (c + a) - b^(5/2 : ℝ) * b + c^(5/2 : ℝ) * (a + b) - c^(5/2 : ℝ) * c - a^(3/2 : ℝ) * b * c - b^(3/2 : ℝ) * c * a - c^(3/2 : ℝ) * a * b := by
      have h_1: a * b * c * (a^(1/2 : ℝ)) = a^(3/2 : ℝ) * b * c := by
        calc a * b * c * (a^(1/2 : ℝ))
          = (a * a^(1/2 : ℝ)) * b * c := by ring
          _ = (a^(1:ℝ) * a^(1/2 : ℝ)) * b * c := by norm_num
          _ = a^(1 + 1/2:ℝ) * b * c := by rw [←Real.rpow_add ha]
          _ = a^(3/2 : ℝ) * b * c := by norm_num

      have h_2: b * c * (b^(1/2 : ℝ)) = b^(3/2 : ℝ) * c := by
        calc b * c * (b^(1/2 : ℝ))
          = (b * b^(1/2 : ℝ)) * c := by ring
          _ = (b^(1:ℝ) * b^(1/2 : ℝ)) * c := by norm_num
          _ = b^(1 + 1/2:ℝ) * c := by rw [←Real.rpow_add hb]
          _ = b^(3/2 : ℝ) * c := by norm_num

      have h_3: c * a * (c^(1/2 : ℝ)) = c^(3/2 : ℝ) * a := by
        calc c * a * (c^(1/2 : ℝ))
          = (c * c^(1/2 : ℝ)) * a := by ring
          _ = (c^(1:ℝ) * c^(1/2 : ℝ)) * a := by norm_num
          _ = c^(1 + 1/2:ℝ) * a := by rw [←Real.rpow_add hc]
          _ = c^(3/2 : ℝ) * a := by norm_num

      rw [← h_1, ←h_2, ←h_3]
      ring
    _ = a^(5/2 : ℝ) * (b + c) - a^(7/2 : ℝ) + b^(5/2 : ℝ) * (c + a) - b^(7/2 : ℝ) + c^(5/2 : ℝ) * (a + b) - c^(7/2 : ℝ) - a^(3/2 : ℝ) * b * c - b^(3/2 : ℝ) * c * a - c^(3/2 : ℝ) * a * b := by
      have h_1:  a^(7/2 : ℝ) = a^(5/2 : ℝ) * a := by
        calc a^(7/2 : ℝ)
          = a^(5/2 + 1 : ℝ) := by norm_num
          _ = a^(5/2 : ℝ) * a^(1 : ℝ) := Real.rpow_add ha _ _
          _ = a^(5/2 : ℝ) * a := by simp

      have h_2:  b^(7/2 : ℝ) = b^(5/2 : ℝ) * b := by
        calc b^(7/2 : ℝ)
          = b^(5/2 + 1 : ℝ) := by norm_num
          _ = b^(5/2 : ℝ) * b^(1 : ℝ) := Real.rpow_add hb _ _
          _ = b^(5/2 : ℝ) * b := by simp

      have h_3:  c^(7/2 : ℝ) = c^(5/2 : ℝ) * c := by
        calc c^(7/2 : ℝ)
          = c^(5/2 + 1 : ℝ) := by norm_num
          _ = c^(5/2 : ℝ) * c^(1 : ℝ) := Real.rpow_add hc _ _
          _ = c^(5/2 : ℝ) * c := by simp

      rw [←h_1, ←h_2, ←h_3]

    _ ≤ 0 := by linarith

  linarith

lemma mean_inequality_pow4 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  (a^(1/2 : ℝ) + b^(1/2 : ℝ) + c^(1/2 : ℝ))/3 ≤ ((a^2 + b^2 + c^2)/3)^(1/4: ℝ) := by
  -- We apply the power‐mean inequality to the multiset {√a, √b, √c} with exponents p = 1 and q = 4.
  -- We index the three numbers by `Fin 3 = {0, 1, 2}`.
  let I := Fin 3
  let s : Finset I := Finset.univ
  -- First, note that `s.card = 3`.
  have hcard : (s.card : ℝ) = 3 := by
    norm_cast


  -- Define the constant weight `w i = 1/3` for all `i : I`.
  let w : I → ℝ := fun _ => (1 : ℝ) / 3
  have hw : ∀ i, 0 ≤ w i := by intro _; norm_num

  -- Check that the weights sum to `1`.
  have hsum : ∑ i ∈ s, w i = 1 := by
    simp only [Finset.sum_const, w, nsmul_eq_mul]
    rw [hcard]
    norm_num

  -- Define `z i = √a`, `√b`, `√c` according to `i = 0, 1, 2`.
  let z : I → ℝ
  | 0 => a^(1/2 : ℝ)
  | 1 => b^(1/2 : ℝ)
  | 2 => c^(1/2 : ℝ)
  -- All `z i` are nonnegative since `a,b,c > 0`.
  have hpos_z : ∀ i, 0 ≤ z i := by
    intro i; fin_cases i <;> positivity

  -- Now apply the weighted power‐mean inequality for `p = 4`:
  --   `∑ w i * z i ≤ (∑ w i * (z i)^4)^(1/4)`,
  -- since `1 ≤ 4`.
  have hp : 1 ≤ (4 : ℝ) := by norm_num
  have h_pm : ∑ i ∈ s, w i * z i ≤ (∑ i ∈ s, w i * z i ^ (4: ℝ)) ^ (1 / 4 : ℝ) := Real.arith_mean_le_rpow_mean s w z (fun i _ => hw i) hsum (fun i hi => hpos_z i) hp

  -- Concretely,
  --  `∑ i ∈ s, w i * z i = (1/3) * (√a + √b + √c)`,
  --  `∑ i ∈ s, w i * (z i)^4 = (1/3) * (a^2 + b^2 + c^2)`.
  have h_sum_z : ∑ i ∈ s, w i * z i = (a^(1/2 : ℝ)+ b^(1/2 : ℝ)+ c^(1/2 : ℝ)) / 3 := by
    -- `∑ i ∈ s, w i * z i = ∑ i ∈ s, (1/3) * z i = (1/3) * ∑ i ∈ s, z i`.
    rw [Fin.sum_univ_three]
    simp [w, z]
    ring

  have h_sum_z4 : ∑ i ∈ s, w i * (z i) ^ (4: ℝ) = (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by
    rw [Fin.sum_univ_three]
    simp only [w, z]
    ring_nf
    repeat rw [← Real.rpow_mul (by positivity)]
    norm_num

  -- Substitute these into the power‐mean conclusion:
  --   `(∑ w i * z i) ≤ (∑ w i * (z i)^4) ^ (1/4)`
  -- becomes
  --   `( (√a + √b + √c) / 3 ) ≤ ( (a^2 + b^2 + c^2) / 3 ) ^ (1/4)`.
  rwa [h_sum_z, h_sum_z4] at h_pm

theorem inequalities_24109
  (a b c : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (h1 : sqrt 2 < min (min (a + b) (b + c)) (c + a))
  (h2 : a^2 + b^2 + c^2 = 3) :
  3 / (a * b * c)^2 ≤ a / (b + c - a)^2 + b / (c + a - b)^2 + c / (a + b - c)^2 := by
  have key1 : min (min (a + b) (b + c)) (c + a) ≤ c + a ∧ min (min (a + b) (b + c)) (c + a) ≤ b + c ∧ min (min (a + b) (b + c)) (c + a) ≤  a + b := by simp [min_le_iff]
  have hh1 : a + b > sqrt 2 := by nlinarith
  have hh2 : b + c > sqrt 2 := by nlinarith
  have hh3 : c + a > sqrt 2 := by nlinarith
  have h31: a^2 + b^2 > 1:= by
    calc _ ≥ (a + b)^2 / 2 := by nlinarith [sq_nonneg (a - b)]
         _ > sqrt 2 ^2 / 2 := by
          gcongr ?_ ^2 /2
         _ = _ := by norm_num
  have h32: b^2 + c^2 > 1:= by
    calc _ ≥ (b + c)^2 / 2 := by nlinarith [sq_nonneg (b - c)]
         _ > sqrt 2 ^2 / 2 := by
          gcongr ?_ ^2 /2
         _ = _ := by norm_num
  have h33: c^2 + a^2 > 1:= by
    calc _ ≥ (c + a)^2 / 2 := by nlinarith [sq_nonneg (c - a)]
         _ > sqrt 2 ^2 / 2 := by
          gcongr ?_ ^2 /2
         _ = _ := by norm_num
  have hasq : a^2 < 2:= by nlinarith
  have hbsq : b^2 < 2:= by nlinarith
  have hcsq : c^2 < 2:= by nlinarith
  have ia : a < sqrt 2 ∧ sqrt 2 < b + c := by
    and_intros
    rw [← Real.sqrt_lt_sqrt_iff_of_pos (show 0 < 2 by norm_num), Real.sqrt_sq (show 0 ≤ a by nlinarith) ] at hasq
    exact hasq
    nlinarith
  have ib : b < sqrt 2 ∧ sqrt 2 < c + a := by
    and_intros
    rw [← Real.sqrt_lt_sqrt_iff_of_pos (show 0 < 2 by norm_num), Real.sqrt_sq (show 0 ≤ b by nlinarith)] at hbsq
    exact hbsq
    nlinarith
  have ic : c < sqrt 2 ∧ sqrt 2 < a + b := by
    and_intros
    rw [← Real.sqrt_lt_sqrt_iff_of_pos (show 0 < 2 by norm_num), Real.sqrt_sq (show 0 ≤ c by nlinarith)] at hcsq
    exact hcsq
    nlinarith
  have Ia : 0 < b + c - a := by linarith
  have Ib : 0 < c + a - b := by linarith
  have Ic : 0 < a + b - c := by linarith

  have h4 : (a^(1/2 : ℝ) + b^(1/2 : ℝ) + c^(1/2 : ℝ)) ≤ 3:= by
    have h_mean: (a^(1/2 : ℝ) + b^(1/2 : ℝ) + c^(1/2 : ℝ))/3 ≤ ((a^2 + b^2 + c^2)/3)^(1/4: ℝ) := mean_inequality_pow4 ha hb hc
    rw [h2] at h_mean
    norm_num at h_mean
    linarith

  have h_ineq : a / (b + c - a)^2 + b / (c + a - b)^2 + c / (a + b - c)^2 ≥ 3 / (a * b * c)^2 := by calc
    _ = ((a^2)^3 / (a^5 * (b + c - a)^2) + (b^2)^3 / (b^5 * (c + a - b)^2) + (c^2)^3 / (c^5 * (a + b - c)^2)) := by field_simp; ring
    _ ≥ (a^2 + b^2 + c^2)^3 / (a^(5 / 2 : ℝ) * (b + c - a) + b^(5 / 2 : ℝ) * (c + a - b) + c^(5 / 2 : ℝ) * (a + b - c))^2 := by
      -- Apply Titu's lemma directly
      exact titu_p_2 ha hb hc Ia Ib Ic
    _ = 27 / (a^(5 / 2 : ℝ) * (b + c - a)+ b^(5 / 2 : ℝ) * (c + a - b) + c^(5 / 2 : ℝ) * (a + b - c))^2 := by simp_rw [h2]; norm_num
    _ ≥ 27 / (a * b * c * (a^(1/2 : ℝ) + b^(1/2 : ℝ) + c^(1/2 : ℝ)))^2 := by
      gcongr
      exact sum_pow_inequality ha hb hc
    _ ≥ 27 / (a * b * c * 3)^2 := by
      gcongr
    _ = 3 / (a * b * c)^2 := by field_simp; ring

  linarith
