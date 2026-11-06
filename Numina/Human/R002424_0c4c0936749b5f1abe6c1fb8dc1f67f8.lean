import Mathlib
open Mathlib

/-- A sequence is defined as follows $a_1=a_2=a_3=1,$ and, for all positive integers $n, a_{n+3}=a_{n+2}+a_{n+1}+a_n.$ Given that $a_{28}=6090307, a_{29}=11201821,$ and $a_{30}=20603361,$ find the remainder when $\sum^{28}_{k=1} a_k$ is divided by 1000. -/
theorem algebra_93185 (a : ℕ → ℤ) (ha1 : a 1 = 1) (ha2 : a 2 = 1) (ha3 : a 3 = 1)
(han : ∀ n > 0, a (n + 3) = a (n + 2) + a (n + 1) + a n)
(h28 : a 28 = 6090307) (h29 : a 29 = 11201821) (h30 : a 30 = 20603361) :
(∑ k in Finset.Icc 1 28, a k) % 1000 = 834 := by
  -- https://artofproblemsolving.com/wiki/index.php/2006_AIME_II_Problems/Problem_11
  have jw n (hn : 0 < n) : (↑(a n) : ℤ) = (↑(a (n + 3)) : ℤ) - (↑(a (n + 2)) : ℤ) - (↑(a (n + 1)) : ℤ) := by zify at *; have := han n hn; linarith
  have je : (∑ k ∈ Finset.Icc 1 28, a k) = (∑ k ∈ Finset.Icc 1 27, a k) + a 28 := by
    rw [← Finset.add_sum_Ico_eq_sum_Icc]
    · rw [(by decide : Finset.Ico 1 28 = Finset.Icc 1 27)]
      rw [add_comm]
    · decide
  /- 
$s = a_{28} + \sum^{27}_{k=1} (a_{k+3}-a_{k+2}-a_{k+1}) \\ s = a_{28} + \left(\sum^{30}_{k=4} a_{k} - \sum^{29}_{k=3} a_{k}\right) - \left(\sum^{28}_{k=2} a_{k}\right)\\ s = a_{28} + (a_{30} - a_{3}) - \left(\sum^{28}_{k=2} a_{k}\right) = a_{28} + a_{30} - a_{3} - (s - a_{1})\\ s = -s + a_{28} + a_{30}$ -/
  have kek n (hn : 0 < n) : ∑ k ∈ Finset.Icc 1 n, a k = ∑ k ∈ Finset.Icc 1 n, (a (k + 3) - a (k + 2) - a (k + 1)) := by
    conv =>
      left
      rw [←Finset.sum_attach]
    conv =>
      right
      rw [←Finset.sum_attach]
    congr
    ext x
    obtain ⟨x, hx⟩ := x
    simp only
    simp only [Finset.mem_Icc] at hx
    rw [jw _ (by linarith)]
  rw [kek 27 (by decide)] at je
  simp only [Finset.sum_sub_distrib] at je
  have shifty (a b c : ℕ) (f : ℕ → ℤ) : ∑ x ∈ Finset.Icc a (a + b), f (x + c) = ∑ x ∈ Finset.Icc (a + c) (a + b + c), f x := by
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
  -- shift sums to subtract
  have aa := shifty 1 26 3
  have bb := shifty 1 26 2
  have cc := shifty 1 26 1
  rw [aa, bb, cc] at je
  norm_num at je
  -- decompose [4, 30]
  have := Nat.Icc_insert_succ_right (a := 4) (b := 29) (by decide)
  norm_num at this
  rw [←this] at je
  -- decompose [3, 29]
  have := Nat.Icc_insert_succ_left (a := 3) (b := 29) (by decide)
  norm_num at this
  rw [←this] at je
  -- change right hand side to a 30 - a 3 - ∑ k ∈ Finset.Icc 2 28, a k + a 28
  conv at je =>
    right
    simp only [Finset.mem_Icc, Nat.reduceLeDiff, and_false, not_false_eq_true, Finset.sum_insert,
      and_true, add_sub_add_right_eq_sub]
  -- express everything in terms of [2, 28]
  have := Nat.Icc_insert_succ_left (a := 1) (b := 28) (by decide)
  norm_num at this
  rw [←this]
  simp only [Finset.mem_Icc, Nat.not_ofNat_le_one, Nat.one_le_ofNat, and_true, not_false_eq_true,
    Finset.sum_insert]
  rw [←this] at je
  simp only [Finset.mem_Icc, Nat.not_ofNat_le_one, Nat.one_le_ofNat, and_true, not_false_eq_true,
    Finset.sum_insert] at je
  simp only [ha1, h30, ha3, Int.reduceSub, h28] at je
  rw [ha1]
  -- calculate
  have kwk : ∑ k ∈ Finset.Icc 2 28, a k = 13346833 := by linarith
  rw [kwk]
  norm_num