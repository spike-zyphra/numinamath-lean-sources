import Mathlib

/-I have written a strictly increasing sequence of six positive integers, such that
each number (besides the first) is a multiple of the one before it,
and the sum of all six numbers is 79 . What is the largest number in my sequence?-/

theorem number_theory_611264 (a b c d e f: ℤ) (ha: 1 ≤ a) (hb: 1 ≤ b) (hc: 1 ≤ c) (hd: 1 ≤ d) (he: 1 ≤ e)
(hab: a < b) (hbc: b < c) (hcd: c < d) (hde: d < e) (hef: e < f) (ab: a ∣ b) (bc: b ∣ c) (cd: c ∣ d)(de: d ∣ e) (ef: e ∣ f)
(hsum: a + b + c + d + e + f = 79) : f = 48 := by
  by_cases bound_d: d ≥ 12
  -- if d ≥ 12- -
  . have bound_e: e ≥ 24 := by  --show that e is at least 24--
      rw [dvd_iff_exists_eq_mul_right] at de
      obtain ⟨k, hk⟩ := de
      have bk: 2 ≤ k := by nlinarith
      rw [hk]
      nlinarith
    have bound_f: f ≥ 48 := by  --show that f is at least 24--
      rw [dvd_iff_exists_eq_mul_right] at ef
      obtain ⟨k, hk⟩ := ef
      have bk: 2 ≤ k := by nlinarith
      rw [hk]
      nlinarith
    -- now d + e + f ≥ 84 > 69, we get a contradiction --
    nlinarith
  . simp at bound_d
    rw [dvd_iff_exists_eq_mul_right] at cd
    obtain ⟨k1,hk1⟩ := cd
    have bk1: 2 ≤ k1 := by nlinarith
    rw [dvd_iff_exists_eq_mul_right] at bc
    obtain ⟨k2,hk2⟩ := bc
    have bk2: 2 ≤ k2 := by nlinarith
    rw [dvd_iff_exists_eq_mul_right] at ab
    obtain ⟨k3,hk3⟩ := ab
    have bk3: 2 ≤ k3 := by nlinarith
    -- now we must have a = 1 --
    have a_val: a = 1 := by
      by_contra! no
      replace no: 2 ≤ a := by omega
      nlinarith
    have b_val: b = 2 := by nlinarith
    have c_val: c = 4 := by
      by_contra! no
      have o: k2 ≥ 3 := by
        by_contra! l
        replace l: k2 = 2 := by omega
        simp [b_val,l] at hk2
        omega
      simp [b_val] at hk2
      nlinarith
    have d_val: d = 8 := by
      simp [c_val] at hk1
      simp [hk1] at bound_d
      have k1l: k1 < 3:= by omega
      replace k1l: k1 = 2 := by omega
      simp [k1l] at hk1
      omega
    simp [a_val,b_val,c_val,d_val] at hsum
    rw [d_val] at hde de
    -- now we clear all the useless hypothesis--
    clear ha hb hc hd hab hbc hcd bound_d hk1 hk2 hk3 bk1 bk2 bk3 a_val b_val c_val a b c d_val d
    rw [dvd_iff_exists_eq_mul_right] at de
    obtain ⟨q,hq⟩ := de
    have bq: 1 < q := by nlinarith
    rw [dvd_iff_exists_eq_mul_right] at ef
    obtain ⟨s,hs⟩ := ef
    have bs: 1 < s := by nlinarith
    simp [hq] at hs
    simp [hs,hq] at hsum
    have eq: q * (1 + s) = 8 := by nlinarith
    have q_val: q = 2 := by nlinarith
    have s_val: s = 3 := by nlinarith
    simp [q_val,s_val] at hs
    exact hs
