import Mathlib

open Set Nat Int

lemma aux {d : ℤ} (h : d ∣ (1 : ℤ)) : d = 1 ∨ d = -1 := by
  rcases h with ⟨k, hk⟩
  have hk' : d * k = 1 := by
    simpa [mul_comm] using hk.symm
  have hprod : (Int.natAbs d) * (Int.natAbs k) = 1 := by
    have := congrArg Int.natAbs hk'
    simpa [Int.natAbs_mul, Int.natAbs_one] using this
  -- Show that abs d = 1
  have h_abs_d : Int.natAbs d = 1 := by
    have hpair := (mul_eq_one).1 hprod
    exact hpair.1
  have h_abs_int : abs d = 1 := by
    linarith
  -- Show that d = -1 or d = 1
  have h_sign : (0 ≤ d) ∨ (d < 0) := le_or_lt 0 d
  cases h_sign with
  | inl h_nonneg =>
      have h_abs_eq : abs d = d :=
        (abs_of_nonneg h_nonneg)
      have : d = 1 := by
        linarith
      exact Or.inl this
  | inr h_neg =>
      have h_abs_eq : abs d = -d :=
        (abs_of_neg h_neg)
      have : d = -1 := by
        linarith
      exact Or.inr this
/-Question: If three integers a,b,c(a≠0) make the equation ax^2+bx+c=0 have two roots a and b, then a+b+c equals 18-/
theorem algebra_296271 (a b c : ℤ) (ha : a ≠ 0) (hab : a ≠ b) (hroots : {a, b} = {x | a * x ^ 2 + b * x + c = 0}) : a + b + c = 18 := by
  -- Expand hroots hypothesis for easier use
  have h1 : a * a ^ 2 + b * a + c = 0 := by
    have : (a) ∈ ({a, b} : Set ℤ) := by
      simp
    have : (a) ∈ ({x | a * x ^ 2 + b * x + c = 0} : Set ℤ) := by
      simpa [hroots]
    exact this
  have h2 : a * b ^ 2 + b * b + c = 0 := by
    have : (b) ∈ ({a, b} : Set ℤ) := by
      simp
    have : (b) ∈ ({x | a * x ^ 2 + b * x + c = 0} : Set ℤ) := by
      simpa [hroots]
    exact this
  -- Derive Vieta's sum and mul result
  have hc : c = - (a * b ^ 2 + b * b) := by
    linarith
  have h3: (a ^ 2 + a * b + b) * (a - b) = 0 := by
    rw [← h1]
    rw [hc]
    ring
  have h4 : a ^ 2 + a * b + b = 0 := by
    rcases (mul_eq_zero.mp h3) with h_left | h_right
    · exact h_left
    · exfalso
      apply sub_ne_zero_of_ne at hab
      exact hab h_right
  -- Show that a=-2
  have a_eq_minus_two : a = -2 := by
    have h5 : (a + 1) * b = - a ^ 2 := by
      ring_nf
      linarith
    have h_dvd :  (a + 1) ∣ - a ^ 2 := by
      apply dvd_of_mul_right_eq at h5
      exact h5
    have h6 : - a ^ 2 =  (a + 1) * (1 - a) + (- 1) := by
      linarith
    rw [h6] at h_dvd
    rw [dvd_add_right] at h_dvd
    rw [dvd_neg] at h_dvd
    have h_eq1 : (a + 1 : ℤ) = 1 ∨ (a + 1) = -1 :=
      aux h_dvd
    field_simp at h_eq1
    have h_eq2 : a + 1 = -1 := by
      tauto
    linarith
    -- Prove that a + 1 ∣ (a + 1) * (1 - a)
    use (1-a)
  -- Show that b=4
  have b_eq_four : b = 4 := by
    rw [a_eq_minus_two] at h4
    linarith
  -- Show that c=16
  have c_eq_sixteen : c = 16 := by
    repeat rw [a_eq_minus_two, b_eq_four] at h1
    linarith
  -- Therefore the sum of a+b+c is 18
  linarith
