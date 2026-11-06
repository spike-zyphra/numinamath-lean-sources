import Mathlib

/- A positive integer $N$ has base-eleven representation
$\underline{a}\underline{b}\underline{c}$ and base-eight representation
$1\underline{b}\underline{c}\underline{a}$, where $a$, $b$, and $c$ represent
(not necessarily distinct) digits. Find the least such $N$ expressed in base ten. -/
theorem number_theory_98108 : IsLeast { N : ℕ | N > 0 ∧ ∃ a b c : ℕ, a < 8 ∧ b < 8 ∧ c < 8 ∧
    N = a * 11 ^ 2 + b * 11 + c ∧ N = 8 ^ 3 + b * 8 ^ 2 + c * 8 + a } 621 := by
  refine ⟨?_, ?_⟩
  -- First we must show that the minimum 621 is achieved, by selecting $a = 5$, $b = 1$, and $c = 5$.
  . exact ⟨by norm_num, ⟨5, 1, 5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
  -- Next we must show that no smaller $N$ satisfies the conditions.
  . intro N h
    rcases h with ⟨hN, a, b, c, ha, hb, hc, hbase11, hbase8⟩
    -- We can combine the two representations of $N$ into one equation.
    have : a * 11 ^ 2 + b * 11 + c = 8 ^ 3 + b * 8 ^ 2 + c * 8 + a := by rw [← hbase11, ← hbase8]
    have eq1 : 120 * a = 512 + 53 * b + 7 * c := by omega
    -- Note that this equation is false if $a < 5$, so we proceed by case analysis comparing $a$ to 5.
    rcases Nat.lt_trichotomy a 5 with (ha5 | rfl | ha5)
    . -- If $a < 5$, we have a contradiction with the equation above.
      have : 480 ≥ 512 := by calc
        480 = 120 * 4 := by norm_num
        _ ≥ 120 * a := Nat.mul_le_mul_left _ (show a ≤ 4 by omega)
        _ = 512 + (53 * b + 7 * c) := by ring_nf; ring_nf at eq1; rw [eq1]
        _ ≥ 512 := by simp
      contradiction
    . -- If $a = 5$, we simplify the combined equation some more and proceed by case analysis on $b$.
      have eq2 : 88 = 53 * b + 7 * c := by omega
      match b with
      | 0 =>
        -- $b = 0$ is impossible as there are no possible values of $c$.
        have : 7 ∣ 88 := by simp at eq2; exact Dvd.intro c (symm eq2)
        contradiction
      | 1 =>
        -- $b = 1$ gives us $c = 5$, so $N = 621$.
        have digitc : c = 5 := by omega
        have : N = 621 := by simp [hbase11, digitc]
        rw [this]
      | n + 2 =>
        -- $b ≥ 2$ is impossible as the right-hand side is too big.
        have : 88 ≥ 106 := by calc
          88 = 106 + (53 * n + 7 * c) := by rw [eq2]; ring
          _ ≥ 106 := by simp
        contradiction
    . -- If $a > 5$, we have N ≥ 621 immediately.
      calc
        N = a * 121 + (b * 11 + c) := by rw [hbase11]; ring
        _ ≥ a * 121 := by simp
        _ ≥ 6 * 121 := Nat.mul_le_mul_right _ (show 6 ≤ a by omega)
        _ ≥ 621 := by simp