import Mathlib

/-
If $k$ is a strictly positive integer, $S(k)$ denotes the sum of the digits in its decimal notation.

1) Are there two strictly positive integers $a$ and $b$ such that $S(a)=S(b)=S(a+b)=2013$?
2) Are there two strictly positive integers $a$ and $b$ such that $S(a)=S(b)=S(a+b)=2016$?
 -/
namespace number_theory_604304

def S k := (Nat.digits 10 k).sum

theorem number_theory_604304 :
    (¬∃ a b, 0 < a ∧ 0 < b ∧ S a = 2013 ∧ S b = 2013 ∧ S (a + b) = 2013) ∧
    (∃ a b, 0 < a ∧ 0 < b ∧ S a = 2016 ∧ S b = 2016 ∧ S (a + b) = 2016) := by
  -- 1. Recall that for any $a$, the integers $a$ and $S(a)$ are congruent modulo 9. Indeed, if $\overline{a_{k} \cdots a_{1} a_{0}}$ is the decimal representation of $a$, then since $10 \equiv 1[9]$, we have for all $j \geqslant 0: 10^{j} \equiv 1^{j}=1[9]$, thus $a=\sum_{j=0}^{k} a_{j} 10^{j} \equiv \sum_{j=0}^{k} a_{j}=S(a)$ \[9\].
  have modEq_9_S a : a ≡ S a [MOD 9] := by
    unfold S
    exact Nat.modEq_nine_digits_sum a
  constructor
  . -- Suppose, for the sake of contradiction, that there exist $a$ and $b$ as described in the statement. Modulo 9, we have
    rintro ⟨a, b, a_pos, b_pos, S_a_eq, S_b_eq, S_a_add_b_eq⟩
    -- $$ \begin{aligned} a & \equiv S(a) \equiv 2013 \equiv 6 \\ b & \equiv S(b) \equiv 2013 \equiv 6 \\ a+b & \equiv S(a+b) \equiv 2013 \equiv 6 \end{aligned} $$
    have a_mod : a ≡ 6 [MOD 9] := by
      have := modEq_9_S a
      --omega
      rw [S_a_eq] at this
      exact this
    have b_mod : b ≡ 6 [MOD 9] := by
      have := modEq_9_S b
      rw [S_b_eq] at this
      exact this
    have a_add_b_mod : a + b ≡ 6 [MOD 9] := by
      have := modEq_9_S (a + b)
      rw [S_a_add_b_eq] at this
      exact this
    -- Adding the first two congruences and subtracting the third, we get $0 \equiv 6+6-6=6 [9]$. Impossible.
    have : a + b ≡ 3 [MOD 9] :=
      have : a + b ≡ 6 + 6 [MOD 9] := by
        gcongr
      this
    have : 6 ≡ 3 [MOD 9] :=
      a_add_b_mod.symm.trans this
    contradiction
  . -- 2) We note that $2016=9 \times 224$, so we can take $\mathrm{a}=\mathrm{b}=9090 \cdots 09$ where the digit 9 appears 224 times, and $a+b=1818 \cdots 18$ where the pattern 18 appears 224 times.
    let a := Nat.ofDigits 10 (List.replicate 224 [0, 9]).flatten
    let b := a
    use a, b
    native_decide

end number_theory_604304
open number_theory_604304
