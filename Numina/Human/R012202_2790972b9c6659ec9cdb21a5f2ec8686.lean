import Mathlib
open Mathlib
/--
How many positive integers less than $1000$ are $6$ times the sum of their digits?
$\textbf{(A)}\ 0 \qquad \textbf{(B)}\ 1 \qquad \textbf{(C)}\ 2 \qquad \textbf{(D)}\ 4 \qquad \textbf{(E)}\ 12$
-/
theorem number_theory_1200 (s : Finset ℕ) (h : ∀ x, x ∈ s ↔ 0 < x ∧ x < 1000 ∧ x = 6 * (Nat.digits 10 x).sum) : s.card = 1 := by
  -- There is only one solution
  have sub : ∀ x, x = 54 ↔ 0 < x ∧ x < 1000 ∧ x = 6 * (Nat.digits 10 x).sum := by
    intro x
    constructor
    -- x = 54 satisfies the conditions
    · intro h
      rw [h]
      simp only [Nat.ofNat_pos, Nat.reduceLT, Nat.reduceLeDiff, Nat.digits_of_two_le_of_pos,
        Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.sum_cons, List.sum_nil, add_zero,
        Nat.reduceAdd, Nat.reduceMul, and_self]
    -- Prove x has to be equal to 54
    rintro ⟨h1, ⟨h2, h3⟩⟩
    have js := Nat.le_digits_len_le 10 x 999 (Nat.le_of_lt_succ h2)
    norm_num at js
    -- each number with this property is divisible by $6$, therefore it is divisible by $3$, and thus also its sum of digits is divisible by $3$. Thus, the number is divisible by $18$.
    have d3 := (Nat.three_dvd_iff x).1 (by rw [h3, (by ring : 6 * (Nat.digits 10 x).sum = 3 * (2 * _))]; apply Nat.dvd_mul_right)
    have we := Nat.mul_dvd_mul_left 6 d3
    rw [← h3] at we
    norm_num at we
    -- x = c * 18
    rw [dvd_def] at we
    rcases we with ⟨c, we⟩
    cases' c with c
    -- c = 0: impossible
    · linarith
    cases' c with c
    -- c = 1: impossible
    · norm_num at we
      rw [we] at h3
      norm_num at h3
    cases' c with c
    -- c = 2: impossible
    · norm_num at we
      rw [we] at h3
      norm_num at h3
    cases' c with c
    -- c = 3: x = 54
    · norm_num at we
      rw [we]
    cases' c with c
    -- c = 4: impossible
    · norm_num at we
      rw [we] at h3
      norm_num at h3
    cases' c with c
    -- c = 5: impossible
    · norm_num at we
      rw [we] at h3
      norm_num at h3
    cases' c with c
    -- c = 6: impossible
    · norm_num at we
      rw [we] at h3
      norm_num at h3
    have jd := Nat.le_digits_len_le 10 108 x (by linarith)
    norm_num at jd
    have kw : (Nat.digits 10 x).length = 3 := Nat.le_antisymm js jd
    rw [List.length_eq_three] at kw
    rcases kw with ⟨a, ⟨b, ⟨w, kw⟩⟩⟩
    rw [kw] at h3
    norm_num at h3
    -- a < 10
    have ay := Nat.digits_lt_base (b := 10) (m := x) (d := a) (by decide) (by simp only [Nat.reduceLeDiff,
      kw, List.mem_cons, List.mem_singleton, true_or])
    -- b < 10
    have ty := Nat.digits_lt_base (b := 10) (m := x) (d := b) (by decide) (by simp only [Nat.reduceLeDiff,
      kw, List.mem_cons, List.mem_singleton, true_or, or_true])
    -- w < 10
    have ag := Nat.digits_lt_base (b := 10) (m := x) (d := w) (by decide) (by simp only [kw, List.mem_cons, List.mem_singleton, true_or, or_true])
    have jek : x ≤ 162 := by linarith
    cases' c with c
    -- x = 126: impossible
    · rw [we] at kw
      norm_num at kw
      linarith
    cases' c with c
    -- x = 144: impossible
    · rw [we] at kw
      norm_num at kw
      linarith
    cases' c with c
    -- x = 162: impossible
    · rw [we] at kw
      norm_num at kw
      linarith
    -- We've considered all cases
    linarith
  simp_rw [← sub] at h
  have sin : s = {54} := by
    ext g
    rw [h]
    simp only [Finset.mem_singleton]
  rw [sin]
  decide