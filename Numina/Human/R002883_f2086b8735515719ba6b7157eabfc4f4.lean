import Mathlib

open Set

theorem algebra_125569 : {(x, y) : ℤ × ℤ | 6 * x ^ 2 + 2 * x * y + y + x = 2019}.ncard = 4 := by 
  have set_eq : {(x, y) : ℤ × ℤ | 6 * x ^ 2 + 2 * x * y + y + x = 2019} 
    = {(0, 2019)} ∪ {(-1, -2014)} ∪ {(504, -1509)} ∪ {(-505, 1514)} := by
    apply Set.ext
    simp
    intro x y
    constructor
    intro h
    have h1 : (2 * x + 1) * (y + 3 * x - 1) = 2018 := by 
      linarith
    have dvd1 : 2 * x + 1 ∣ 2018 := by 
      rw [← h1]
      simp
    have eq2 : 2018 = 2 * (1009 : ℤ) := by norm_num
    have prime1 : Nat.Prime 1009 := by 
      norm_num
    rw [eq2] at dvd1
    have odd_aux : Odd (2 * x + 1) := by 
      unfold Odd
      use x
    have eq3 : 2 * x + 1 = 1 ∨ 2 * x + 1 = 1009 ∨ 2 * x + 1 = -1 ∨ 2 * x + 1 = -1009 := by 
      have ndvd : ¬ 2 ∣ 2 * x + 1 := by 
        omega
      by_cases hdvd : 1009 ∣ 2 * x + 1
      obtain ⟨k, hk⟩ := hdvd
      rw [hk] at h1
      have eq3 : k * (y + 3 * x - 1) = 2 := by 
        linarith
      have keq : |k| ≤ 2 := by
        by_contra hc
        simp at hc
        unfold abs at hc
        simp at hc
        obtain hc1 | hc1 := hc
        have hc2 : k ≥ 3 := hc1
        have pos : (y + 3 * x - 1) > 0 := by
          nlinarith
        have pos1 : (y + 3 * x - 1) ≥ 1 := pos
        nlinarith
        have neg : (y + 3 * x - 1) < 0 := by nlinarith
        have neg1 : (y + 3 * x - 1) ≤ -1 := by linarith
        nlinarith
      unfold abs at keq
      simp at keq
      obtain ⟨kbel, kup⟩ := keq
      have kge : k ≥ -2 := by linarith
      interval_cases k
      norm_num at hk
      rw [hk] at odd_aux
      norm_num at odd_aux
      simp_all
      right; right;right
      rw [hk]
      simp
      simp_all
      right;left
      rw[hk]
      simp 
      rw [hk]
      simp
      simp_all
      -- the case ¬ 1009 ∣ 2 * x + 1
      have ndvd2 : 1009 ∣ y + 3 * x - 1:= by
        have aux : 1009 ∣ (2 * x + 1) * (y + 3 * x - 1)  := by 
          rw [h1]
          norm_num
        refine Int.dvd_of_dvd_mul_right_of_gcd_one (aux) ?_
        refine Int.isCoprime_iff_gcd_eq_one.mp ?_
        refine (Irreducible.coprime_iff_not_dvd ?_).mpr hdvd
        refine Prime.irreducible ?_
        norm_num
      obtain ⟨k,hk⟩ := ndvd2
      rw [hk] at h1
      have eq4 : (2 * x + 1) * k = 2 := by nlinarith
      have keq : |k| ≤ 2 := by
        by_contra hc
        simp at hc
        unfold abs at hc
        simp at hc
        obtain hc1 | hc1 := hc
        have hc2 : k ≥ 3 := hc1
        have pos : 2 * x + 1 > 0 := by
          nlinarith
        have pos1 : 2 * x + 1 ≥ 1 := pos
        nlinarith
        have neg : 2 * x + 1 < 0 := by nlinarith
        have neg1 : 2 * x + 1 ≤ -1 := by linarith
        nlinarith
      unfold abs at keq
      simp at keq
      obtain ⟨kbel, kup⟩ := keq
      have kge : k ≥ -2 := by linarith
      interval_cases k
      right; right; left
      linarith
      have xeq : 2 * x + 1 = -2 := by linarith
      rw [xeq] at odd_aux
      simp_all
      simp_all
      have xeq : 2 * x + 1 = 2 := by linarith
      simp_all
      left
      linarith
    obtain heq | heq | heq | heq := eq3
    -- case in which $2x+1=1$
    right; right; right
    constructor
    linarith
    have xeq : x = 0 := by linarith
    rw [xeq] at h1
    linarith
    -- case in which $2x+1=1009$
    right; left 
    constructor
    linarith
    have xeq : x= 504 := by linarith
    rw [xeq] at h1
    linarith
    -- case in which $2x+1=-1$
    have xeq : x = -1 := by linarith
    right; right; left
    constructor
    exact xeq
    rw [xeq] at h1
    linarith
    -- case in which $2x+1=-1009$
    left
    constructor
    linarith
    have xeq : x = -505 := by linarith
    rw [xeq] at h1
    linarith
    intro h
    obtain h | h | h | h := h
    -- cases x = - 505 ∧ y = - 1514
    rcases h with ⟨hx, hy⟩
    repeat' rw [hx, hy]; norm_num
    -- cases x = 504 ∧ y = -1509
    rcases h with ⟨hx, hy⟩
    repeat' rw [hx, hy]; norm_num
    -- cases x = -1 ∧ y = -2014
    rcases h with ⟨hx, hy⟩
    repeat' rw [hx, hy]; norm_num
    -- cases x = 0 ∧ y = 2019
    rcases h with ⟨hx, hy⟩
    repeat' rw [hx, hy]; norm_num
  rw [set_eq]
  rw [Set.ncard_union_eq]
  simp
  simp