import Mathlib
/-- Find the arithmetic mean of all the three-digit palindromes. (Recall that a palindrome is a number that reads the same forward and backward, such as $777$ or $383$.) -/
theorem number_theory_42922 :
(∑ n in (Finset.Icc 100 999).filter (fun n => Nat.digits 10 n = List.reverse (Nat.digits 10 n)), n) / ((Finset.Icc 100 999).filter (fun n => Nat.digits 10 n = List.reverse (Nat.digits 10 n))).card = 550 := by
  -- first we provide an alternative construction which is much easier to manipulate
  have re : (Finset.Icc 100 999).filter (fun n => Nat.digits 10 n = List.reverse (Nat.digits 10 n)) = (Finset.Icc 1 9 ×ˢ Finset.Icc 0 9).attach.map (⟨fun ⟨⟨a, b⟩, c⟩ => 100 * a + 10 * b + a, fun ⟨⟨a, b⟩, c⟩ ⟨⟨a1, b1⟩, c1⟩ h => by {
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at *
    have ha : a ∈ Finset.Icc 1 9 := by aesop
    have hb : b ∈ Finset.Icc 0 9 := by aesop
    have ha1 : a1 ∈ Finset.Icc 1 9 := by aesop
    have hb1 : b1 ∈ Finset.Icc 0 9 := by aesop
    clear c c1
    simp only [Finset.mem_Icc, zero_le, true_and] at ha hb ha1 hb1
    omega
  }⟩) := by
    ext x
    simp only [Nat.reduceLeDiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_map,
      Finset.mem_attach, Function.Embedding.coeFn_mk, true_and, Subtype.exists, Finset.mem_product,
      zero_le, exists_prop, Prod.exists]
    symm
    constructor <;> intro h
    · obtain ⟨a, b, h⟩ := h
      constructor
      · omega
      -- split into constituent digits
      · rw [Nat.digits_def' (b := 10) (by norm_num) (by omega)]
        rw [Nat.digits_def' (b := 10) (by norm_num) (by omega)]
        rw [Nat.digits_def' (b := 10) (by norm_num) (by omega)]
        rw [(by rw [Nat.div_div_eq_div_mul]; omega : x / 10 / 10 / 10 = 0)]
        simp only [Nat.reduceLeDiff, Nat.digits_zero, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append, List.cons.injEq, and_true, true_and]
        simp only [Nat.div_div_eq_div_mul]
        obtain ⟨⟨⟨h1, h4⟩, h2⟩, h3⟩ := h
        subst x
        norm_num
        -- split into 3 subtasks so omega can solve
        rw [(by omega : (100 * a + 10 * b + a) % 10 = a), (by omega : (100 * a + 10 * b + a) / 100 = a)]
        omega
    · exists x / 100, x / 10 % 10
      obtain ⟨h1, h2⟩ := h
      -- clear off first leg
      constructor; · omega
      -- split into constituent digits
      rw [Nat.digits_def' (b := 10) (by norm_num) (by omega)] at h2
      rw [Nat.digits_def' (b := 10) (by norm_num) (by omega)] at h2
      rw [Nat.digits_def' (b := 10) (by norm_num) (by omega)] at h2
      rw [(by rw [Nat.div_div_eq_div_mul]; omega : x / 10 / 10 / 10 = 0)] at h2
      simp only [Nat.reduceLeDiff, Nat.digits_zero, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.cons.injEq, and_true, true_and] at h2
      simp only [Nat.div_div_eq_div_mul] at h2
      norm_num at h2
      -- algebra
      rw [(by omega : x / 100 % 10 = x / 100)] at h2
      obtain ⟨h3, h4⟩ := h2
      conv =>
        left; right; rw [h4]
      omega
  rw [re]; clear re
  -- we now have a neater term to manipulate
  rw [Finset.card_map, Finset.card_attach]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Finset.card_product, Nat.card_Icc,
    Nat.reduceAdd, Nat.add_one_sub_one, tsub_zero, Nat.reduceMul]
  have g := Finset.sum_attach (Finset.Icc 1 9 ×ˢ Finset.Icc 0 9) (fun ⟨a, b⟩ => 100 * a + 10 * b + a)
  simp only at g; rw [g]; clear g
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_product, Finset.sum_const,
    Nat.card_Icc, Nat.reduceAdd, tsub_zero, smul_eq_mul, Nat.add_one_sub_one]
  -- there are only sums over [1, 9] and [0, 9] which could be computed quickly, therefore per guidelines native_decide is justified
  native_decide