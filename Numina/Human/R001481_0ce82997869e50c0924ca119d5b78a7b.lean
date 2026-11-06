import Mathlib

open Real
/- Some auxiliary lemmas: (4 : ℝ) ^ (1 / 3 : ℝ) = 2 ^ (2 / 3 : ℝ) -/
lemma four_pow_one_div_three : (4 : ℝ) ^ (1 / 3 : ℝ) = 2 ^ (2 / 3 : ℝ) := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by ring, ←rpow_mul (by simp), mul_one_div]

/- Some auxiliary lemmas: (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) = 2 -/
lemma four_pow_one_div_mul_four_pow_two_div : (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) = 2 := by
  rw [←rpow_add (by simp)]
  norm_num

/- Some auxiliary lemmas: (2 ^ (1 / 3 : ℝ)) ^ 2 = (2 : ℝ) ^ (2 / 3 : ℝ) -/
lemma sq_pow_one_div_eq_pow_two_div : (2 ^ (1 / 3 : ℝ)) ^ 2 = (2 : ℝ) ^ (2 / 3 : ℝ) := by
  rw [←rpow_natCast, ←rpow_mul (by simp), one_div_mul_eq_div]
  rfl

/- Some auxiliary lemmas: (2 ^ (2 / 3 : ℝ)) ^ 2 = 2 * (2 : ℝ) ^ (1 / 3 : ℝ)-/
lemma sq_pow_twpo_div_eq_two_mul_pow_one_div : (2 ^ (2 / 3 : ℝ)) ^ 2 = 2 * (2 : ℝ) ^ (1 / 3 : ℝ) := by
  rw [←rpow_natCast, ←rpow_mul (by simp)]
  trans (2 : ℝ) ^ (1 + 1 / 3 : ℝ)
  · norm_num
  · rw [rpow_add (by simp), rpow_one]

/- Prove that a (n + 1) = a n - 8 * b n + 8 * c n ∧ b (n + 1) = 4 * a n + b n - 8 * c n ∧ c (n + 1) = c n - 4 * a n + 4 * b n  -/
lemma a_b_c_succ {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n))
    (n : ℕ) :
    a (n + 1) = a n - 8 * b n + 8 * c n ∧ b (n + 1) = 4 * a n + b n - 8 * c n ∧ c (n + 1) = c n - 4 * a n + 4 * b n := by
  have h : (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ (n + 1) =
      (a n - 8 * b n + 8 * c n : ℤ) + (4 * a n + b n - 8 * c n : ℤ) * (2 : ℝ) ^ ((1 : ℝ) / 3) + (c n - 4 * a n + 4 * b n : ℤ) * (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    push_cast
    rw [pow_add, hexist n, pow_one]
    simp only [four_pow_one_div_three]
    ring_nf
    rw [sq_pow_one_div_eq_pow_two_div, sq_pow_twpo_div_eq_two_mul_pow_one_div]
    rw [mul_assoc (b n : ℝ), four_pow_one_div_mul_four_pow_two_div]
    rw [mul_comm _ (c n : ℝ), mul_assoc (c n : ℝ), four_pow_one_div_mul_four_pow_two_div]
    ring_nf
  apply hunique at h
  simp [←h]

/- Show that a 0 = 1, b0 = 0, c 0 = 0. -/
lemma a_b_c_zero {a b c : ℕ → ℤ}
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n)) :
    a 0 = 1 ∧ b 0 = 0 ∧ c 0 = 0 := by
  obtain h := hunique 0 1 0 0
  simp at h
  simp [←h]

/- Show that a (m + n) = a m * a n + 2 * b m * c n + 2 * c m * b n, b (m + n) = a m * b n + b m * a n + 2 * c m * c n, c (m + n) = a m * c n + c m * a n + b m * b n -/
lemma a_b_c_add {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n))
    (m n : ℕ) :
    a (m + n) = a m * a n + 2 * b m * c n + 2 * c m * b n ∧ b (m + n) = a m * b n + b m * a n + 2 * c m * c n ∧ c (m + n) = a m * c n + c m * a n + b m * b n := by
  have h : (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ (m + n) =
      (a m * a n + 2 * b m * c n + 2 * c m * b n : ℤ) + (a m * b n + b m * a n + 2 * c m * c n : ℤ) * (2 : ℝ) ^ ((1 : ℝ) / 3) + (a m * c n + c m * a n + b m * b n : ℤ) * (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    push_cast
    rw [pow_add, hexist n, hexist m]
    simp only [four_pow_one_div_three]
    ring_nf
    rw [sq_pow_one_div_eq_pow_two_div, sq_pow_twpo_div_eq_two_mul_pow_one_div]
    rw [mul_assoc (b m : ℝ), four_pow_one_div_mul_four_pow_two_div]
    rw [mul_comm _ (c m : ℝ), mul_assoc (c m : ℝ), four_pow_one_div_mul_four_pow_two_div]
    ring_nf
  apply hunique at h
  simp [←h]

/- Show that a (2 ^ (p + 1)) = a (2 ^ p) ^ 2 + 4 * b (2 ^ p) * c (2 ^ p),
    b (2 ^ (p + 1)) = 2 * a (2 ^ p) * b (2 ^ p) + 2 * c (2 ^ p) ^ 2,
    c (2 ^ (p + 1)) = 2 * a (2 ^ p) * c (2 ^ p) + b (2 ^ p) ^ 2 -/
lemma a_b_c_pow_succ {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n))
    (p : ℕ) :
    a (2 ^ (p + 1)) = a (2 ^ p) ^ 2 + 4 * b (2 ^ p) * c (2 ^ p) ∧
    b (2 ^ (p + 1)) = 2 * a (2 ^ p) * b (2 ^ p) + 2 * c (2 ^ p) ^ 2 ∧
    c (2 ^ (p + 1)) = 2 * a (2 ^ p) * c (2 ^ p) + b (2 ^ p) ^ 2 := by
  have : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
  obtain h := a_b_c_add hexist hunique (2 ^ p) (2 ^ p)
  rw [this, h.1, h.2.1, h.2.2]
  split_ands
  all_goals ring

/- padicValInt 2 (-x) = padicValInt 2 x -/
lemma padicValInt_neg {x : ℤ} : padicValInt 2 (-x) = padicValInt 2 x := by
  unfold padicValInt
  simp

/- padicValInt 2 (x ^ n : ℤ) = n * padicValInt 2 x -/
lemma padicValInt_pow (hx : x ≠ 0) : padicValInt 2 (x ^ n : ℤ) = n * padicValInt 2 x := by
  unfold padicValInt
  rw [Int.natAbs_pow, padicValNat.pow]
  simp [hx]

/- Show that ¬ 2 ∣ (a n) -/
lemma two_not_dvd_a {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n)) :
    ¬ 2 ∣ (a n) := by
  -- prove by induction on n
  induction n with
  | zero =>
    -- ¬ 2 ∣ a 0 = 1
    simp [a_b_c_zero hunique]
  | succ n ih =>
    -- a (n + 1) = a n - 8 * b n + 8 * c n
    -- 2 ∣ 8 but ¬ 2 ∣ a n
    -- thus ¬ 2 ∣ (a n - 8 * b n + 8 * c n)
    rw [(a_b_c_succ hexist hunique n).1]
    simp at ih ⊢
    rw [Int.add_emod, Int.sub_emod, ih]
    simp [Int.mul_emod]

/- Show that padicValInt 2 (a n) = 0 -/
lemma padicValInt_a {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n)) :
    padicValInt 2 (a n) = 0 := by
  -- Since ¬ 2 ∣ (a n), we have that padicValInt 2 (a n) = 0
  refine padicValInt.eq_zero_of_not_dvd ?_
  exact two_not_dvd_a hexist hunique

/-  padicValInt 2 2 = 1 -/
lemma padicValInt_two : padicValInt 2 2 = 1 := by
  rw [show (2 : ℤ) = (2 : ℕ) by simp, padicValInt.self]
  simp

/- If padicValInt 2 a < padicValInt 2 b, then padicValInt 2 (a + b) = padicValInt 2 a -/
lemma padicValInt_add {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hlt : (padicValInt 2 a : ℤ) < padicValInt 2 b) : padicValInt 2 (a + b) = padicValInt 2 a := by
  suffices : padicValInt 2 (a + b) = (padicValInt 2 a : ℤ)
  · norm_cast at this
  · rw [←padicValRat.of_int, ←padicValRat.of_int, Int.cast_add]
    rw [padicValRat.add_eq_of_lt]
    · by_contra h
      have ha : a = -b := by
        norm_cast at h
        exact eq_neg_of_add_eq_zero_left h
      simp [ha, padicValInt_neg] at hlt
    · simp [ha]
    · simp [hb]
    · simp [padicValRat.of_int, hlt]

/- Prove that padicValInt 2 (b (2 ^ p)) = padicValInt 2 (c (2 ^ p)) = p + 2 -/
lemma padic_two_pow {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n))
    {p : ℕ} :
    padicValInt 2 (c (2 ^ p)) = p + 2 ∧ padicValInt 2 (b (2 ^ p)) = p + 2 := by
  -- prove by induction on p
  induction p with
  | zero =>
    -- If p = 0, then a 1 = 1, b 1 = 4, c 1 = -4.
    obtain h := a_b_c_succ hexist hunique 0
    simp [a_b_c_zero hunique] at h
    simp [h]
    rw [show (4 : ℤ) = 2 ^ 2 by ring, padicValInt_neg, padicValInt_pow]
    · simp [padicValInt_two]
    · simp
  | succ p ih =>
    -- We have shown that a (2 ^ (p + 1)) = a (2 ^ p) ^ 2 + 4 * b (2 ^ p) * c (2 ^ p) ∧
    -- b (2 ^ (p + 1)) = 2 * a (2 ^ p) * b (2 ^ p) + 2 * c (2 ^ p) ^ 2 ∧
    -- c (2 ^ (p + 1)) = 2 * a (2 ^ p) * c (2 ^ p) + b (2 ^ p) ^ 2
    obtain h := a_b_c_pow_succ hexist hunique p
    have ha : a (2 ^ p) ≠ 0 := by
      obtain h := two_not_dvd_a hexist hunique (n := 2 ^ p)
      intro ha
      simp [ha] at h
    have hb : b (2 ^ p) ≠ 0 := by
      by_contra h
      simp [h] at ih
    have hc : c (2 ^ p) ≠ 0 := by
      by_contra h
      simp [h] at ih
    rw [h.2.2, h.2.1]
    -- Applying ih, we can obtain the results.
    have h1 : padicValInt 2 (2 * ↑(a (2 ^ p)) * ↑(b (2 ^ p))) = p + 3 := by
      rw [padicValInt.mul (by simp [ha]), padicValInt.mul ?_ (by simp [ha]), padicValInt_a hexist hunique, padicValInt_two, ih.2]
      · ring
      all_goals simp [hb]
    have h2 : padicValInt 2 (2 * ↑(a (2 ^ p)) * ↑(c (2 ^ p))) = p + 3 := by
      rw [padicValInt.mul (by simp [ha]), padicValInt.mul ?_ (by simp [ha]), padicValInt_a hexist hunique, padicValInt_two, ih.1]
      · ring
      all_goals simp [hc]
    have h3 : padicValInt 2 (2 * c (2 ^ p) ^ 2) = 2 * p + 5 := by
      rw [padicValInt.mul (by simp [ha]), padicValInt_pow, padicValInt_two, ih.1]
      · ring
      all_goals simp [hc]
    have h4 : padicValInt 2 (b (2 ^ p) ^ 2) = 2 * p + 4 := by
      rw [padicValInt_pow, ih.2]
      · ring
      all_goals simp [hb]
    constructor
    · rw [padicValInt_add, h2]
      · simp [ha, hc]
      · simp [hb]
      · simp [h2, h4]
        apply sub_pos.mp
        ring_nf
        positivity
    · rw [padicValInt_add, h1]
      · simp [ha, hb]
      · simp [hc]
      · simp [h1, h3]
        apply sub_pos.mp
        ring_nf
        positivity

/- If padicValInt 2 (b m) = padicValInt 2 (c m) ∧ padicValInt 2 (b n) = padicValInt 2 (c n) and padicValInt 2 (c n) > padicValInt 2 (c m), padicValInt 2 (c m) > 0, then
  padicValInt 2 (b (m + n)) = padicValInt 2 (c (m + n)) = padicValInt 2 (c m) -/
lemma padic_add {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n))
    {m n : ℕ} (hm : padicValInt 2 (b m) = padicValInt 2 (c m)) (hn : padicValInt 2 (b n) = padicValInt 2 (c n)) (hlt : padicValInt 2 (c n) > padicValInt 2 (c m)) (hmne : padicValInt 2 (c m) > 0) :
    padicValInt 2 (b (m + n)) = padicValInt 2 (c (m + n)) ∧ padicValInt 2 (c (m + n)) = padicValInt 2 (c m) := by
  -- We have proved that b (m + n) = a m * b n + b m * a n + 2 * c m * c n ∧
  -- c (m + n) = a m * c n + c m * a n + b m * b n
  obtain h := a_b_c_add hexist hunique m n
  rw [h.2.1, h.2.2]
  have ham : (a m) ≠ 0 := by
    obtain h := two_not_dvd_a hexist hunique (n := m)
    intro ham
    simp [ham] at h
  have han : (a n) ≠ 0 := by
    obtain h := two_not_dvd_a hexist hunique (n := n)
    intro han
    simp [han] at h
  have hcm : (c m) ≠ 0 := by
    by_contra h
    simp [h] at hmne
  have hbm : (b m) ≠ 0 := by
    by_contra h
    simp [h] at hm
    simp [←hm] at hmne
  have hcn : (c n) ≠ 0 := by
    by_contra h
    simp [h] at hlt
  have hbn : (b n) ≠ 0 := by
    by_contra h
    simp [h] at hn
    simp [←hn] at hlt
  -- Applying ih, we can directly compute the results.
  have h₁ : padicValInt 2 (a m * b n) = padicValInt 2 (c n) := by rw [padicValInt.mul ham hbn, padicValInt_a hexist hunique, hn, zero_add]
  have h₂ : padicValInt 2 (b m * a n) = padicValInt 2 (c m) := by rw [padicValInt.mul hbm han, padicValInt_a hexist hunique, hm, add_zero]
  have h₃ : padicValInt 2 (2 * c m * c n) = padicValInt 2 (c m) + padicValInt 2 (c n) + 1 := by
    rw [padicValInt.mul (by simp [hcm]) hcn, padicValInt.mul (by simp) hcm, padicValInt_two]
    ring
  have h₄ : padicValInt 2 (a m * c n) = padicValInt 2 (c n) := by rw [padicValInt.mul ham hcn, padicValInt_a hexist hunique, zero_add]
  have h₅ : padicValInt 2 (c m * a n) = padicValInt 2 (c m) := by rw [padicValInt.mul hcm han, padicValInt_a hexist hunique, add_zero]
  have h₆ : padicValInt 2 (b m * b n) = padicValInt 2 (c m) + padicValInt 2 (c n) := by rw [padicValInt.mul hbm hbn, hm, hn]
  have h₇ : padicValInt 2 (a m * b n + b m * a n) = padicValInt 2 (c m) := by
    rw [add_comm, padicValInt_add, h₂]
    · positivity
    · positivity
    · simp [h₁, h₂]
      exact hlt
  have h₈ :  padicValInt 2 (a m * c n + c m * a n) = padicValInt 2 (c m) := by
    rw [add_comm, padicValInt_add, h₅]
    · positivity
    · positivity
    · simp [h₄, h₅]
      exact hlt
  have h₉ : padicValInt 2 (a m * b n + b m * a n + 2 * c m * c n) = padicValInt 2 (c m) := by
    rw [padicValInt_add, h₇]
    · intro h
      simp [h] at h₇
      simp [←h₇] at hmne
    · positivity
    · simp [h₇, h₃]
      apply sub_pos.mp
      ring_nf
      positivity
  have h₁₀ : padicValInt 2 (a m * c n + c m * a n + b m * b n) = padicValInt 2 (c m) := by
    rw [padicValInt_add, h₈]
    · intro h
      simp [h] at h₈
      simp [←h₈] at hmne
    · positivity
    · simp [h₈, h₆]
      apply lt_trans ?_ hlt
      positivity
  simp [h₉, h₁₀]

/- Show that if L1.length = L2.length, then Nat.ofDigits is injective. -/
lemma ofDigits_inj_of_len_eq {b : ℕ} (hb : 1 < b) {L1 L2 : List ℕ} (len : L1.length = L2.length) (w1 : ∀ l ∈ L1, l < b) (w2 : ∀ l ∈ L2, l < b) (h : Nat.ofDigits b L1 = Nat.ofDigits b L2) :
    L1 = L2 := by
  induction' L1 with D L ih generalizing L2
  · simp only [List.length_nil] at len
    symm
    exact List.length_eq_zero.mp (id (Eq.symm len))
  obtain ⟨d, l, rfl⟩ := List.exists_cons_of_length_eq_add_one len.symm
  simp only [List.length_cons, add_left_inj] at len
  simp only [Nat.ofDigits_cons] at h
  have eqd : D = d := by
    have H : (D + b * Nat.ofDigits b L) % b = (d + b *  Nat.ofDigits b l) % b := by rw [h]
    simp at H
    simpa [Nat.mod_eq_of_lt (w2 d (List.mem_cons_self d l)), Nat.mod_eq_of_lt (w1 D (List.mem_cons_self D L))] using H
  simp only [eqd, add_right_inj, mul_left_cancel_iff_of_pos ( Nat.zero_lt_of_lt hb)] at h
  have := ih len (fun a ha ↦ w1 a <| List.mem_cons_of_mem D ha)
    (fun a ha ↦ w2 a <| List.mem_cons_of_mem d ha) h
  rw [eqd, this]

/- Show that Nat.ofDigits b (l ++ List.replicate k 0) = Nat.ofDigits b l -/
lemma ofDigits_append_replicate_zero {b k : ℕ} (l : List ℕ) : Nat.ofDigits b (l ++ List.replicate k 0) = Nat.ofDigits b l := by
  rw [Nat.ofDigits_append]
  suffices h : Nat.ofDigits b (List.replicate k 0) = 0
  · simp [h]
  · induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate, Nat.ofDigits_cons, ih]

/- Show that padicValInt 2 (b n) = padicValInt 2 (c n) = List.indexOf 1 (Nat.digits 2 n) + 2 -/
lemma padic_c {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n))
    (hn : n > 0) :
    padicValInt 2 (b n) = padicValInt 2 (c n) ∧ padicValInt 2 (c n) = List.indexOf 1 (Nat.digits 2 n) + 2 := by
  -- prove by induction on the length of Nat.digits 2 n
  set l := Nat.digits 2 n with hl
  set k := l.length with ←hk
  clear_value l k
  simp [hl]
  induction k using Nat.strong_induction_on generalizing l n
  rename_i k ih
  by_cases hk_cases : k = 0
  · -- If k = 0, then l = [] and n = 0, which is a contradiction.
    simp [hk_cases] at hk
    simp [hk, Nat.digits_eq_nil_iff_eq_zero] at hl
    simp [hl] at hn
  · -- If k > 0, then l ≠ []。
    simp at hk_cases
    let k' := k - 1
    have hk' : k = k' + 1 := by
      rw [Nat.sub_add_cancel]
      exact Nat.one_le_iff_ne_zero.mpr hk_cases
    simp [hk'] at hk
    -- Assume that l = l' ++ [a] where a is the last element of l.
    let a := l.getLast (by exact List.ne_nil_of_length_eq_add_one hk)
    let l' := l.dropLast
    have hl' : l = l' ++ [a] := by
      simp [l', a]
      exact Eq.symm (List.dropLast_concat_getLast (List.ne_nil_of_length_eq_add_one hk))
    have hlength_l' : l'.length = k' := by
      simp [hl'] at hk
      exact hk
    have hmem_l' : ∀ x ∈ l', x < 2 := by
      intro x hx
      have : x ∈ Nat.digits 2 n := by
        simp [←hl, hl', hx]
      exact Nat.digits_lt_base' this
    -- We have n = Nat.ofDigits 2 l' + a * 2 ^ l'.length.
    have hn_eq : n = Nat.ofDigits 2 (l' ++ [a]) := by
      rw [←hl', hl]
      exact Eq.symm (Nat.ofDigits_digits 2 n)
    simp [Nat.ofDigits_append] at hn_eq
    -- Since a ∈ l, we have a < 2.
    -- We also have a ≠ 0 since a is the last element of l.
    have ⟨ha₁, ha₂⟩ : a ≠ 0 ∧  a < 2 := by
      have : a = (Nat.digits 2 n).getLast (by simp [←hl, hl']) := by simp [←hl]
      rw [this]
      constructor
      · apply Nat.getLast_digit_ne_zero
        exact Nat.not_eq_zero_of_lt hn
      · apply Nat.digits_lt_base (by simp)
        apply List.getLast_mem
    interval_cases a
    · simp at ha₁
    · -- Therefore, a = 1 and we have n = Nat.ofDigits 2 l' + 2 ^ l'.length
      simp at hn_eq
      -- Let n' := Nat.ofDigits 2 l'
      set n' := Nat.ofDigits 2 l' with hn'
      let l'' := Nat.digits 2 n'
      by_cases hn'_zero : n' = 0
      · -- If n' = 0, then n = 2 ^ l'.length.
        simp [hn'_zero] at hn_eq
        have : Nat.digits 2 n = List.replicate l'.length 0 ++ [1] := by
          trans Nat.digits 2 (n * 1)
          · simp
          · rw [hn_eq, Nat.digits_base_pow_mul]
            all_goals simp
        -- We have prove that padicValInt 2 (b n) = padicValInt 2 (c n) = l'.length + 2.
        rw [this, hn_eq, (padic_two_pow hexist hunique).1, (padic_two_pow hexist hunique).2, List.indexOf_append_of_not_mem]
        all_goals simp
      · -- If n' > 0, then assume taht l'' = Nat.digits 2 n'.
        have hn'_pos : n' > 0 := by exact Nat.zero_lt_of_ne_zero hn'_zero
        -- Obviously, l'' ≠ [] and l''.length < k.
        have hl''_ne_nil : l'' ≠ [] := by
          intro h
          have : Nat.digits 2 n' = [] := by
            apply Eq.trans rfl h
          apply Nat.digits_eq_nil_iff_eq_zero.mp at this
          simp [this] at hn'_pos
        have hl'' : l''.length < k := by
          have h₀ : 2 ^ l''.length ≤ 2 * n' := by
            simp [l'']
            exact Nat.base_pow_length_digits_le' 0 n' hn'_zero
          have h₁ : 2 * n' < 2 ^ (1 + l'.length) := by
            simp [n', pow_add]
            refine Nat.ofDigits_lt_base_pow_length ha₂ ?_
            exact fun x a ↦ hmem_l' x a
          apply lt_of_le_of_lt h₀ at h₁
          have : l''.length < 1 + l'.length := by exact (Nat.pow_lt_pow_iff_right ha₂).mp h₁
          apply lt_of_lt_of_eq this
          trans l.length
          · simp [hl']; ring
          · simp [hk, k', Nat.sub_add_cancel]
            exact id (Eq.symm hk')
        -- We also have l' = l'' ++ List.replicate (l'.length - l''.length) 0.
        have hl'_eq : l' = l'' ++ List.replicate (l'.length - l''.length) 0 := by
          apply ofDigits_inj_of_len_eq (b := 2) (by simp)
          · simp
            rw [Nat.add_sub_cancel']
            trans k'
            · simp [k']
              exact Nat.le_sub_one_of_lt hl''
            · exact Nat.le_of_eq (id (Eq.symm hlength_l'))
          · exact fun l a ↦ hmem_l' l a
          · intro x hx
            simp at hx
            rcases hx with hx | hx
            · simp [l''] at hx
              exact Nat.digits_lt_base' hx
            · simp [hx.2]
          · simp [ ofDigits_append_replicate_zero, l'']
            trans n'
            · rfl
            · exact Eq.symm (Nat.ofDigits_digits 2 n')
        have hone_mem : 1 ∈ l'' := by
          have : l''.getLast hl''_ne_nil = 1 := by
            have ⟨h, _⟩ : l''.getLast hl''_ne_nil ≠ 0 ∧ l''.getLast hl''_ne_nil < 2 := by
              simp [l'']
              constructor
              · exact Nat.getLast_digit_ne_zero 2 hn'_zero
              · apply Nat.digits_lt_base (by simp)
                apply List.getLast_mem
            interval_cases l''.getLast hl''_ne_nil
            · simp at h
            · simp
          simp [←this]
        -- Apply ih on l''.length and n', we have padicValInt 2 (b n') = padicValInt 2 (c n') = List.indexOf 1 (Nat.digits 2 n') + 2
        obtain ih := ih l''.length hl'' hn'_pos l'' rfl rfl
        nth_rw 1 2 3 [hn_eq]
        -- Apply padicValInt_add, we have padicValInt 2 (b (n' + 2 ^ l'.length)) = padicValInt 2 (c (n' + 2 ^ l'.length)) = padicValInt 2 (c (n'))
        obtain h : padicValInt 2 (b (n' + 2 ^ l'.length)) = padicValInt 2 (c (n' + 2 ^ l'.length)) ∧ padicValInt 2 (c (n' + 2 ^ l'.length)) = padicValInt 2 (c (n')) := by
          apply padic_add hexist hunique ih.1
          any_goals simp [padic_two_pow hexist hunique]
          · rw [ih.2]
            simp
            apply lt_of_lt_of_le (b := l''.length)
            · apply List.indexOf_lt_length.mpr hone_mem
            · trans k'
              · exact Nat.le_sub_one_of_lt hl''
              · exact Nat.le_of_eq (id (Eq.symm hlength_l'))
          · simp [ih.2]
        rw [h.1, h.2, ih.2]
        constructor
        · simp
        · congr 1
          rw [←hl, hl', hl'_eq, List.indexOf_append_of_mem, List.indexOf_append_of_mem hone_mem]
          simp [List.mem_append, hone_mem]

/- 9. (FRA 4) For all integers $n, n \geq 0$, there exist uniquely determined integers $a_{n}, b_{n}, c_{n}$ such that
$$ (1+4 \sqrt[3]{2}-4 \sqrt[3]{4})^{n}=a_{n}+b_{n} \sqrt[3]{2}+c_{n} \sqrt[3]{4} $$  Prove that $c_{n}=0$ implies $n=0$. -/
theorem algebra_24266 {a b c : ℕ → ℤ}
    (hexist : ∀ n, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a n + b n * (2 : ℝ) ^ ((1 : ℝ) / 3) + c n * (4 : ℝ) ^ ((1 : ℝ) / 3))
    (hunique : ∀ n, ∀ a' b' c' : ℤ, (1 + 4 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 4 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ n = a' + b' * (2 : ℝ) ^ ((1 : ℝ) / 3) + c' * (4 : ℝ) ^ ((1 : ℝ) / 3) → (a' = a n ∧ b' = b n ∧ c' = c n)) :
    ∀ n, c n = 0 → n = 0 := by
  intro n hc
  -- Asusme that c n = 0 and n > 0.
  by_contra h
  have hn : n > 0 := by exact Nat.zero_lt_of_ne_zero h
  -- Then we have that padicValInt 2 (c n) =  List.indexOf 1 (Nat.digits 2 n) + 2 ≥ 2.
  obtain h := padic_c hexist hunique hn
  -- However, we also have that padicValInt 2 (c n) = 0, which contradicts the above result.
  simp [hc] at h
