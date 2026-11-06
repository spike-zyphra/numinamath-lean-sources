import Mathlib

def d : ℕ → ℕ
| n => (∑ i in Finset.Icc 1 n, i) % 10

/-- For a positive integer $n$, let $d_n$ be the units digit of $1 + 2 + \dots + n$. Find the remainder when\[\sum_{n=1}^{2017} d_n\]is divided by $1000$. -/
theorem number_theory_97041 : (∑ n in Finset.Icc 1 2017, d n) % 1000 = 69 := by
  -- lemma to shift the range of a sum
  have shifty (a b c : ℕ) (f : ℕ → ℕ) : ∑ x ∈ Finset.Icc a (a + b), f (x + c) = ∑ x ∈ Finset.Icc (a + c) (a + b + c), f x := by
    clear * -
    induction b with
    | zero =>
      simp only [add_zero, Finset.Icc_self, Finset.sum_singleton, implies_true]
    | succ b IH =>
      rw [(by ring : a + (b + 1) = (a + b) + 1), (by ring : a + b + 1 + c = a + b + c + 1)]
      repeat rw [← Nat.Icc_insert_succ_right]
      simp only [Finset.mem_Icc, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
        and_false, not_false_eq_true, Finset.sum_insert]
      rw [IH]
      rw [(by ring : a + b + 1 + c = a + b + c + 1)]
      all_goals linarith

  -- decompose d (a + b)
  have dd (a b : ℕ) : d (a + b) = (d a + (∑ i in Finset.Icc (a + 1) (a + b), i) % 10) % 10 := by
    induction b with
    | zero => simp only [d, add_zero, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt,
      Finset.Icc_eq_empty_of_lt, Finset.sum_empty, Nat.zero_mod, dvd_refl, Nat.mod_mod_of_dvd]
    | succ b IH =>
      simp only [d, Nat.add_mod_mod, Nat.mod_add_mod]
      simp only [d, Nat.add_mod_mod, Nat.mod_add_mod] at IH
      rw [←add_assoc]
      rw [←@Nat.Icc_insert_succ_right 1 (a + b) (by linarith), ←@Nat.Icc_insert_succ_right (a + 1) (a + b) (by linarith)]
      simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true, Finset.sum_insert]
      rw [Nat.add_mod, IH]
      simp only [Nat.add_mod_mod, Nat.mod_add_mod]
      ring_nf

  -- prove a neat property of d (a + b) to help facilitate proving the cyclic nature of d
  have ee (a b : ℕ) : d (a + b) = (d a + d b + a * b) % 10 := by
    rw [dd]
    cases b with
    | zero =>
      simp only [d, add_zero, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt,
        Finset.Icc_eq_empty_of_lt, Finset.sum_empty, Nat.zero_mod, dvd_refl, Nat.mod_mod_of_dvd,
        mul_zero]
    | succ b =>
      have := shifty 1 b a id
      rw [(by ring : 1 + a = a + 1), (by ring : 1 + b + a = a + (b + 1))] at this
      simp only [id_eq] at this
      rw [←this]
      rw [Finset.sum_add_distrib]
      have ee : d (b + 1) = (∑ x ∈ Finset.Icc 1 (1 + b), x) % 10 := by
        simp only [d]
        rw [add_comm]
      simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, smul_eq_mul,
        Nat.add_mod_mod]
      rw [Nat.add_mod]
      conv =>
        left
        left
        right
        rw [Nat.add_mod, ←ee]
      simp only [Nat.add_mod_mod, Nat.mod_add_mod]
      ring_nf

  -- We see that $d_n$ appears in cycles of $20$ and the cycles are\[1,3,6,0,5,1,8,6,5,5,6,8,1,5,0,6,3,1,0,0,\]
  have cycle n : d (20 * n + 0) = 0 ∧ d (20 * n + 1) = 1 ∧ d (20 * n + 2) = 3 ∧ d (20 * n + 3) = 6 ∧ d (20 * n + 4) = 0 ∧ d (20 * n + 5) = 5 ∧ d (20 * n + 6) = 1 ∧ d (20 * n + 7) = 8 ∧ d (20 * n + 8) = 6 ∧ d (20 * n + 9) = 5 ∧ d (20 * n + 10) = 5 ∧ d (20 * n + 11) = 6 ∧ d (20 * n + 12) = 8 ∧ d (20 * n + 13) = 1 ∧ d (20 * n + 14) = 5 ∧ d (20 * n + 15) = 0 ∧ d (20 * n + 16) = 6 ∧ d (20 * n + 17) = 3 ∧ d (20 * n + 18) = 1 ∧ d (20 * n + 19) = 0 := by
    induction n with
    | zero => native_decide
    | succ n IH =>
      ring_nf
      simp only [add_comm _ (n * 20)]
      simp only [mul_comm n 20]
      obtain ⟨IH0, IH1, IH2, IH3, IH4, IH5, IH6, IH7, IH8, IH9, IH10, IH11, IH12, IH13, IH14, IH15, IH16, IH17, IH18, IH19⟩ := IH
      -- we decompose the calls to the function d
      have nha0 := ee (20 * n + 0) 20; have nha1 := ee (20 * n + 1) 20; have nha2 := ee (20 * n + 2) 20; have nha3 := ee (20 * n + 3) 20; have nha4 := ee (20 * n + 4) 20; have nha5 := ee (20 * n + 5) 20; have nha6 := ee (20 * n + 6) 20; have nha7 := ee (20 * n + 7) 20; have nha8 := ee (20 * n + 8) 20; have nha9 := ee (20 * n + 9) 20; have nha10 := ee (20 * n + 10) 20; have nha11 := ee (20 * n + 11) 20; have nha12 := ee (20 * n + 12) 20; have nha13 := ee (20 * n + 13) 20; have nha14 := ee (20 * n + 14) 20; have nha15 := ee (20 * n + 15) 20; have nha16 := ee (20 * n + 16) 20; have nha17 := ee (20 * n + 17) 20; have nha18 := ee (20 * n + 18) 20; have nha19 := ee (20 * n + 19) 20
      rw [add_assoc] at *
      norm_num at *
      have il : d 20 = 0 := by native_decide
      rw [il] at nha0 nha1 nha2 nha3 nha4 nha5 nha6 nha7 nha8 nha9 nha10 nha11 nha12 nha13 nha14 nha15 nha16 nha17 nha18 nha19
      norm_num at *
      -- we rewrite with the induction hypothesis
      rw [IH0] at nha0; rw [IH1] at nha1; rw [IH2] at nha2; rw [IH3] at nha3; rw [IH4] at nha4; rw [IH5] at nha5; rw [IH6] at nha6; rw [IH7] at nha7; rw [IH8] at nha8; rw [IH9] at nha9; rw [IH10] at nha10; rw [IH11] at nha11; rw [IH12] at nha12; rw [IH13] at nha13; rw [IH14] at nha14; rw [IH15] at nha15; rw [IH16] at nha16; rw [IH17] at nha17; rw [IH18] at nha18; rw [IH19] at nha19
      rw [nha0, nha1, nha2, nha3, nha4, nha5, nha6, nha7, nha8, nha9, nha10, nha11, nha12, nha13, nha14, nha15, nha16, nha17, nha18, nha19]
      clear * -
      omega

  have te : (∑ n ∈ Finset.Icc 1 20, d n) = 70 := by native_decide

  -- decompose into full cycles
  have err (i : ℕ) : ∑ n ∈ Finset.Icc 1 (20 * i), d n = i * ∑ n ∈ Finset.Icc 1 20, d n := by
    induction i with
    | zero => native_decide
    | succ i IH =>
      rw [(by ring : 20 * (i + 1) = 20 * i + 20), te]
      rw [te] at IH
      repeat (rw [←@Nat.Icc_insert_succ_right 1 _ (by linarith)]; simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true, Finset.sum_insert])
      simp only [add_assoc]; norm_num
      norm_num at cycle
      obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19⟩ := cycle i
      rw [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19]
      rw [(by ring : 20 * i + 20 = 20 * (i + 1))]
      obtain ⟨k20, _⟩ := cycle (i + 1)
      rw [k20]
      simp only [←add_assoc]
      norm_num
      rw [IH]
      ring

  have can := err 100
  obtain ⟨w, ww⟩: ∃ x, x = 2000 := ⟨2000, rfl⟩
  rw [(by rw [ww] : 2017 = w + 17)]
  -- unroll 17 iterations
  repeat (rw [Nat.add_succ, ←@Nat.Icc_insert_succ_right 1 _ (by norm_num)]; simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true, Finset.sum_insert]; rw [add_assoc]; norm_num)
  simp only [←add_assoc]
  rw [ww]
  norm_num
  -- rewrite sum from 1 to 2000
  norm_num at can
  rw [can, te]
  -- handle the 17 remaining terms
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19⟩ := cycle 100
  norm_num at *
  simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19]
  decide