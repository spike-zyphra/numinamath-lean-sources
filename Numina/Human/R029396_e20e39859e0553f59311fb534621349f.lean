import Mathlib
/-- Recall that a palindrome is a number that reads the same forward and backward. Find the greatest integer less than $1000$ that is a palindrome both when written in base ten and when written in base eight, such as $292 = 444_{\text{eight}}.$ -/
theorem number_theory_98659 :
IsGreatest {n | n < 1000 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ Nat.digits 8 n = List.reverse (Nat.digits 8 n)} 585 := by
  constructor
  -- witness
  · native_decide
  -- optimality
  · intros n hn
    obtain ⟨ht, hp, he⟩ := hn
    by_contra hc
    simp only [not_le] at hc
    -- n has 4 digits in base 8
    rw [Nat.digits_def' (b := 8) (by norm_num) (by omega)] at he
    rw [Nat.digits_def' (b := 8) (by norm_num) (by omega)] at he
    rw [Nat.digits_def' (b := 8) (by norm_num) (by omega)] at he
    rw [Nat.digits_def' (b := 8) (by norm_num) (by omega)] at he
    rw [(by simp only [Nat.div_div_eq_div_mul]; omega : n / 8 / 8 / 8 / 8 = 0)] at he; simp only [Nat.reduceLeDiff,
      Nat.digits_zero, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.cons.injEq, and_true] at he
    simp only [Nat.div_div_eq_div_mul] at he; norm_num at he
    have wla : n = 512 * (n / 512) + 64 * (n / 64 % 8) + 8 * (n / 8 % 8) + n % 8 := by omega
    have alw : n / 512 % 8 = n / 512 := by omega
    rw [alw] at he
    -- we ascertain that n / 512 = 1
    have aw : n / 512 = 1 := by omega
    obtain ⟨e1, e2, e3, e4⟩ := he
    rw [e1, e2, aw] at wla; ring_nf at wla
    -- there are only 8 possible choices for n / 64 % 8
    have wal : n / 64 % 8 = 0 ∨ n / 64 % 8 = 1 ∨ n / 64 % 8 = 2 ∨ n / 64 % 8 = 3 ∨ n / 64 % 8 = 4 ∨ n / 64 % 8 = 5 ∨ n / 64 % 8 = 6 ∨ n / 64 % 8 = 7 := by clear * -; omega
    obtain a | a | a | a | a | a | a | a := wal
    -- clear most cases
    all_goals rw [a] at wla; norm_num at wla; rw [wla] at hp; simp only [Nat.digits, Nat.reduceAdd,
      Nat.digitsAux, Nat.reduceMod, Nat.reduceDiv, Nat.digitsAux_zero, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.cons.injEq, Nat.reduceEqDiff,
      and_true, and_false, and_self] at hp
    -- only n / 64 % 8 = 5 remains
    -- which means n = 585
    subst n; norm_num at hc